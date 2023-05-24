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

data IsNormSubst : Subst ctx ctx' -> Type where
  Base : IsNormSubst (Base thin)
  (:<) : IsNormSubst sub -> IsNormal t -> IsNormSubst (sub :< t)

%name IsNormSubst prf

record NormSubst (ctx, ctx' : SnocList Ty) where
  constructor MkNormSubst
  forget : Subst ctx ctx'
  0 isNormSubst : IsNormSubst forget

%name NormSubst sub

indexNormal : IsNormSubst sub -> (i : Elem ty ctx) -> IsNormal (index sub i)
indexNormal Base i = Ntrl Var
indexNormal (sub :< t) Here = t
indexNormal (sub :< t) (There i) = indexNormal sub i

index : NormSubst ctx' ctx -> Elem ty ctx -> Normal ctx' ty
index sub i = MkNormal (index (forget sub) i) (indexNormal (isNormSubst sub) i)

restrictNormal : IsNormSubst sub -> (thin : ctx3 `Thins` ctx2) -> IsNormSubst (restrict sub thin)
restrictNormal Base thin = Base
restrictNormal (sub :< t) Id = sub :< t
restrictNormal (sub :< t) (Drop thin) = restrictNormal sub thin
restrictNormal (sub :< t) (Keep thin) = restrictNormal sub thin :< t

restrict : NormSubst ctx1 ctx2 -> ctx3 `Thins` ctx2 -> NormSubst ctx1 ctx3
restrict sub thin =
  MkNormSubst
    (restrict (forget sub) thin)
    (restrictNormal (isNormSubst sub) thin)

data Case : Type -> Type where
  Eval :
    Term ctx ty ->
    NormSubst ctx' ctx ->
    Case (Normal ctx' ty)
  EvalSub :
    Subst ctx' ctx ->
    NormSubst ctx'' ctx' ->
    Case (NormSubst ctx'' ctx)
  App :
    Normal ctx (ty ~> ty') ->
    Normal ctx ty ->
    Case (Normal ctx ty')
  Rec :
    Normal ctx N ->
    Normal ctx ty ->
    Normal (ctx :< ty) ty ->
    Case (Normal ctx ty)

partial
eval : Case ret -> Cont (ret)
eval (Eval (Var i) sub) = pure (index sub i)
eval (Eval (Abs t) sub) = do
  sub <- eval (EvalSub (forget sub) (MkNormSubst (Base $ Drop Id) Base))
  let sub = MkNormSubst (forget sub :< Var Here) (isNormSubst sub :< Ntrl Var)
  t <- eval (Eval t sub)
  pure (MkNormal (Abs $ forget t) (Abs $ isNormal t))
eval (Eval (App t u) sub) = do
  t <- eval (Eval t sub)
  u <- eval (Eval u sub)
  eval (App t u)
eval (Eval (Zero) sub) = pure (MkNormal Zero Zero)
eval (Eval (Succ t) sub) = {forget $= Succ, isNormal $= Succ} <$> eval (Eval t sub)
eval (Eval (Rec t u v) sub) = do
  t <- eval (Eval t sub)
  u <- eval (Eval u sub)
  sub <- eval (EvalSub (forget sub) (MkNormSubst (Base $ Drop Id) Base))
  let sub = MkNormSubst (forget sub :< Var Here) (isNormSubst sub :< Ntrl Var)
  v <- eval (Eval v sub)
  eval (Rec t u v)
eval (Eval (Sub t sub') sub) = do
  sub' <- eval (EvalSub sub' sub)
  eval (Eval t sub')
eval (EvalSub (Base thin) sub') = pure (restrict sub' thin)
eval (EvalSub (sub :< t) sub') =
  pure (\sub, t => MkNormSubst (forget sub :< forget t) (isNormSubst sub :< isNormal t)) <*>
  eval (EvalSub sub sub') <*>
  eval (Eval t sub')
eval (App (MkNormal (Abs t) prf) u) =
  eval (Eval t (MkNormSubst (Base Id :< forget u) (Base :< isNormal u)))
eval (App (MkNormal t@(Var _) prf) u) =
  pure (MkNormal (App t (forget u)) (Ntrl $ App Var (isNormal u)))
eval (App (MkNormal t@(App _ _) prf) u) =
  pure (MkNormal (App t (forget u)) (Ntrl $ App (appNtrl prf) (isNormal u)))
eval (App (MkNormal t@(Rec _ _ _) prf) u) =
  pure (MkNormal (App t (forget u)) (Ntrl $ App (recNtrl prf) (isNormal u)))
eval (Rec (MkNormal Zero prf) u v) = pure u
eval (Rec (MkNormal (Succ t) prf) u v) = do
  val <- eval (Rec (MkNormal t (predNorm prf)) u v)
  eval (Eval (forget v) (MkNormSubst (Base Id :< forget val) (Base :< isNormal val)))
eval (Rec (MkNormal t@(Var _) prf) u v) =
  pure $
  MkNormal (Rec t (forget u) (forget v)) (Ntrl $ Rec Var (isNormal u) (isNormal v))
eval (Rec (MkNormal t@(App _ _) prf) u v) =
  pure $
  MkNormal (Rec t (forget u) (forget v)) (Ntrl $ Rec (appNtrl prf) (isNormal u) (isNormal v))
eval (Rec (MkNormal t@(Rec _ _ _) prf) u v) =
  pure $
  MkNormal (Rec t (forget u) (forget v)) (Ntrl $ Rec (recNtrl prf) (isNormal u) (isNormal v))
