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

data Case : Type -> Type where
  Eval : Term ctx ty -> NormSubst ctx' ctx -> Case (Normal ctx' ty)
  EvalSub : Subst ctx' ctx -> NormSubst ctx'' ctx' -> Case (NormSubst ctx'' ctx)
  App : Normal ctx (ty ~> ty') -> Normal ctx ty -> Case (Normal ctx ty')
  Rec : Normal ctx N -> Normal ctx ty -> Normal (ctx :< ty) ty -> Case (Normal ctx ty)

partial
eval : Case ret -> Cont (ret)
eval (Eval (Var i) sub) = pure (index sub i)
eval (Eval (Abs t) sub) = [| Abs (eval (Eval t (lift sub))) |]
eval (Eval (App t u) sub) = do
  t <- eval (Eval t sub)
  u <- eval (Eval u sub)
  eval (App t u)
eval (Eval (Zero) sub) = pure Zero
eval (Eval (Succ t) sub) = [| Succ (eval (Eval t sub)) |]
eval (Eval (Rec t u v) sub) = do
  t <- eval (Eval t sub)
  u <- eval (Eval u sub)
  v <- eval (Eval v (lift sub))
  eval (Rec t u v)
eval (Eval (Sub t sub') sub) = do
  sub' <- eval (EvalSub sub' sub)
  eval (Eval t sub')
eval (EvalSub (Base thin) sub') = pure (restrict sub' thin)
eval (EvalSub (sub :< t) sub') =
  [| eval (EvalSub sub sub') :< eval (Eval t sub') |]
eval (App (Abs t) u) =
  eval (Eval (forgetNorm t) (Base Id :< u))
eval (App (Ntrl t) u) = pure (Ntrl $ App t u)
eval (Rec (Zero) u v) = pure u
eval (Rec (Succ t) u v) = do
  val <- eval (Rec t u v)
  eval (Eval (forgetNorm v) (Base Id :< val))
eval (Rec (Ntrl t) u v) = pure (Ntrl $ Rec t u v)
