module Level0

import Data.SnocList.Elem
import NormalForm
import Term
import Thinning

record Cont (a : Type) where
  constructor Then
  runCont : forall res. (a -> res) -> res

Functor Cont where
  map f (Then g) = Then (\k => k (g f))

Applicative Cont where
  pure x = Then (\k => k x)
  Then f <*> Then v = Then (\k => f (\j => v (k . j)))

Monad Cont where
  join (Then f) = Then (\k => f (\c => runCont c k))

public export
data NormSubst : SnocList Ty -> SnocList Ty -> Type where
  Base : ctx' `Thins` ctx -> NormSubst ctx ctx'
  (:<) : NormSubst ctx ctx' -> Normal ctx ty -> NormSubst ctx (ctx' :< ty)

%name NormSubst sub

shift : NormSubst ctx ctx' -> NormSubst (ctx :< ty) ctx'
shift (Base thin) = Base (Drop thin)
shift (sub :< t) = shift sub :< wknNorm t (Drop Id)

lift : NormSubst ctx ctx' -> NormSubst (ctx :< ty) (ctx' :< ty)
lift (Base thin) = Base (keep thin)
lift (sub :< t) = shift (sub :< t) :< Ntrl (Var Here)

index : NormSubst ctx' ctx -> Elem ty ctx -> Normal ctx' ty
index (Base thin) i = Ntrl (Var $ index thin i)
index (sub :< t) Here = t
index (sub :< t) (There i) = index sub i

restrict : NormSubst ctx1 ctx2 -> ctx3 `Thins` ctx2 -> NormSubst ctx1 ctx3
restrict (Base thin') thin = Base (thin' . thin)
restrict (sub :< t) Id = sub :< t
restrict (sub :< t) (Drop thin) = restrict sub thin
restrict (sub :< t) (Keep thin) = restrict sub thin :< t

-- Evaluates a term in a context of normal forms.
partial
eval : Term ctx ty -> NormSubst ctx' ctx -> Cont (Normal ctx' ty)
partial
evalSub : Subst ctx ctx'' -> NormSubst ctx' ctx -> Cont (NormSubst ctx' ctx'')
partial
rec : Normal ctx N -> Normal ctx ty -> Normal (ctx :< ty) ty -> Cont (Normal ctx ty)

eval (Var i) sub = pure (index sub i)
eval (Abs t) sub = [| Abs (eval t $ lift sub) |]
eval (App t u) sub = do
  t <- eval t sub
  case t of
    Abs t => do
      u <- eval u sub
      eval (forgetNorm t) (Base Id :< u)
    Ntrl t => Ntrl <$> App t <$> eval u sub
eval Zero sub = pure Zero
eval (Succ t) sub = [| Succ (eval t sub) |]
eval (Rec t u v) sub = do
  t <- eval t sub
  u <- eval u sub
  v <- eval v (lift sub)
  rec t u v
eval (Sub t sub') sub = do
  sub' <- evalSub sub' sub
  eval t sub'

evalSub (Base thin) sub' = pure (restrict sub' thin)
evalSub (sub :< t) sub' = [| evalSub sub sub' :< eval t sub' |]

rec Zero u v = pure u
rec (Succ t) u v = do
  val <- rec t u v
  eval (forgetNorm v) (Base Id :< val)
rec (Ntrl t) u v = pure (Ntrl $ Rec t u v)
