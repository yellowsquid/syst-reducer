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

data Case : Type where
  Eval : (0 ty : Ty) -> (0 ctx, ctx' : SnocList Ty) -> Case
  EvalSub : (0 ctx, ctx', ctx'' : SnocList Ty) -> Case
  App : (0 ty, ty' : Ty) -> (0 ctx : SnocList Ty) -> Case
  Rec : (0 ty : Ty) -> (0 ctx : SnocList Ty) -> Case

0 Input : Case -> Type
Input (Eval ty ctx ctx') = (Term ctx ty, NormSubst ctx' ctx)
Input (EvalSub ctx ctx' ctx'') = (Subst ctx' ctx, NormSubst ctx'' ctx')
Input (App ty ty' ctx) = (Normal ctx (ty ~> ty'), Normal ctx ty)
Input (Rec ty ctx) = (Normal ctx N, Normal ctx ty, Normal (ctx :< ty) ty)

0 Output : Case -> Type
Output (Eval ty ctx ctx') = Normal ctx' ty
Output (EvalSub ctx ctx' ctx'') = NormSubst ctx'' ctx
Output (App ty ty' ctx) = Normal ctx ty'
Output (Rec ty ctx) = Normal ctx ty

partial
eval : (c : Case) -> Input c -> Cont (Output c)
eval (Eval _ _ _) (Var i, sub) = pure (index sub i)
eval (Eval _ _ _) (Abs t, sub) = [| Abs (eval (Eval _ _ _) (t, lift sub)) |]
eval (Eval _ _ _) (App t u, sub) = do
  t <- eval (Eval _ _ _) (t, sub)
  u <- eval (Eval _ _ _) (u, sub)
  eval (App _ _ _) (t, u)
eval (Eval _ _ _) (Zero, sub) = pure Zero
eval (Eval _ _ _) (Succ t, sub) = [| Succ (eval (Eval _ _ _) (t, sub)) |]
eval (Eval _ _ _) (Rec t u v, sub) = do
  t <- eval (Eval _ _ _) (t, sub)
  u <- eval (Eval _ _ _) (u, sub)
  v <- eval (Eval _ _ _) (v, lift sub)
  eval (Rec _ _) (t, u, v)
eval (Eval _ _ _) (Sub t sub', sub) = do
  sub' <- eval (EvalSub _ _ _) (sub', sub)
  eval (Eval _ _ _) (t, sub')
eval (EvalSub _ _ _) (Base thin, sub') = pure (restrict sub' thin)
eval (EvalSub _ _ _) (sub :< t, sub') =
  [| eval (EvalSub _ _ _) (sub, sub') :< eval (Eval _ _ _) (t, sub') |]
eval (App _ _ _) (Abs t, u) =
  eval (Eval _ _ _) (forgetNorm t, Base Id :< u)
eval (App _ _ _) (Ntrl t, u) = pure (Ntrl $ App t u)
eval (Rec _ _) (Zero, u, v) = pure u
eval (Rec _ _) (Succ t, u, v) = do
  val <- eval (Rec _ _) (t, u, v)
  eval (Eval _ _ _) (forgetNorm v, Base Id :< val)
eval (Rec _ _) (Ntrl t, u, v) = pure (Ntrl $ Rec t u v)
