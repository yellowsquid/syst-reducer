module Level1

import Data.DPair
import Data.SnocList.Elem
import NormalForm
import Term
import Thinning

%hide NormalForm.Normal

data IsNormSubst : Subst ctx ctx' -> Type where
  Base : IsNormSubst (Base thin)
  (:<) : IsNormSubst sub -> IsNormal t -> IsNormSubst (sub :< t)

%name IsNormSubst prf

Normal : SnocList Ty -> Ty -> Type
Normal ctx ty = Subset (Term ctx ty) IsNormal

NormSubst : SnocList Ty -> SnocList Ty -> Type
NormSubst ctx ctx' = Subset (Subst ctx ctx') IsNormSubst

indexNormal : IsNormSubst sub -> (i : Elem ty ctx) -> IsNormal (index sub i)
indexNormal Base i = Ntrl Var
indexNormal (sub :< t) Here = t
indexNormal (sub :< t) (There i) = indexNormal sub i

index : NormSubst ctx' ctx -> Elem ty ctx -> Normal ctx' ty
index sub i = Element (index (fst sub) i) (indexNormal (snd sub) i)

restrictNormal : IsNormSubst sub -> (thin : ctx3 `Thins` ctx2) -> IsNormSubst (restrict sub thin)
restrictNormal Base thin = Base
restrictNormal (sub :< t) Id = sub :< t
restrictNormal (sub :< t) (Drop thin) = restrictNormal sub thin
restrictNormal (sub :< t) (Keep thin) = restrictNormal sub thin :< t

restrict : NormSubst ctx1 ctx2 -> ctx3 `Thins` ctx2 -> NormSubst ctx1 ctx3
restrict sub thin = Element (restrict (fst sub) thin) (restrictNormal (snd sub) thin)

data Value : Type where
  V : (ctx : SnocList Ty) -> (ty : Ty) -> Value
  S : (ctx, ctx' : SnocList Ty) -> Value

Raw : Value -> Type
Raw (V ctx ty) = Term ctx ty
Raw (S ctx ctx') = Subst ctx ctx'

Norm : (a : Value) -> Raw a -> Type
Norm (V _ _) = IsNormal
Norm (S _ _) = IsNormSubst

data Cont : Value -> Value -> Type where
  EvalAbs1 : Term (ctx :< ty) ty' -> Cont (S (ctx' :< ty) ctx) (V ctx' (ty ~> ty'))
  EvalAbs2 : Cont (V (ctx :< ty) ty') (V ctx (ty ~> ty'))
  EvalApp1 : Term ctx ty -> NormSubst ctx' ctx -> Cont (V ctx' (ty ~> ty')) (V ctx' ty')
  EvalApp2 : Normal ctx (ty ~> ty') -> Cont (V ctx ty) (V ctx ty')
  EvalSucc1 : Cont (V ctx N) (V ctx N)
  EvalRec1 :
    Term ctx ty ->
    Term (ctx :< ty) ty ->
    NormSubst ctx' ctx ->
    Cont (V ctx' N) (V ctx' ty)
  EvalRec2 :
    Normal ctx' N ->
    Term (ctx :< ty) ty ->
    NormSubst ctx' ctx ->
    Cont (V ctx' ty) (V ctx' ty)
  EvalRec3 :
    Normal ctx' N ->
    Normal ctx' ty ->
    Term (ctx :< ty) ty ->
    Cont (S (ctx' :< ty) ctx) (V ctx' ty)
  EvalRec4 :
    Normal ctx N ->
    Normal ctx ty ->
    Cont (V (ctx :< ty) ty) (V ctx ty)
  EvalSub1 : Term ctx ty -> Cont (S ctx' ctx) (V ctx' ty)
  EvalSnoc1 :
    Term ctx ty ->
    NormSubst ctx' ctx ->
    Cont (S ctx' ctx'') (S ctx' (ctx'' :< ty))
  EvalSnoc2 : NormSubst ctx' ctx -> Cont (V ctx' ty) (S ctx' (ctx :< ty))
  RecSucc1 : Normal (ctx :< ty) ty -> Cont (V ctx ty) (V ctx ty)

data Stack : Value -> Value -> Type where
  Nil : Stack a a
  (::) : Cont a b -> Stack b c -> Stack a c

%name Cont k
%name Stack stack

data Case : Value -> Type where
  Eval : Term ctx ty -> NormSubst ctx' ctx -> Case (V ctx' ty)
  EvalSub : Subst ctx' ctx -> NormSubst ctx'' ctx' -> Case (S ctx'' ctx)
  App : Normal ctx (ty ~> ty') -> Normal ctx ty -> Case (V ctx ty')
  Rec : Normal ctx N -> Normal ctx ty -> Normal (ctx :< ty) ty -> Case (V ctx ty)
  Run : Subset (Raw a) (Norm a) -> Case a

%name Case c

%prefix_record_projections off

record Config (ret : Value) where
  constructor On
  {0 a : Value}
  c : Case a
  stack : Stack a ret

data NotDone : Config ret -> Type where
  EvalNotDone : NotDone (Eval t sub `On` stack)
  EvalSubNotDone : NotDone (EvalSub sub sub' `On` stack)
  AppNotDone : NotDone (App t u `On` stack)
  RecNotDone : NotDone (Rec t u v `On` stack)
  RunSomeNotDone : NotDone (Run x `On` step :: stack)

step : (config : Config ret) -> {auto 0 _ : NotDone config} -> Config ret
step (Eval (Var i) sub `On` stack) =
  Run (index sub i) `On`
  stack
step (Eval (Abs t) sub `On` stack) =
  EvalSub (fst sub) (Element (Base $ Drop Id) Base) `On`
  EvalAbs1 t :: stack
step (Eval (App t u) sub `On` stack) =
  Eval t sub `On`
  EvalApp1 u sub :: stack
step (Eval Zero sub `On` stack) =
  Run (Element Zero Zero) `On`
  stack
step (Eval (Succ t) sub `On` stack) =
  Eval t sub `On`
  EvalSucc1 :: stack
step (Eval (Rec t u v) sub `On` stack) =
  Eval t sub `On`
  EvalRec1 u v sub :: stack
step (Eval (Sub t sub') sub `On` stack) =
  EvalSub sub' sub `On`
  EvalSub1 t :: stack
step (EvalSub (Base thin) sub' `On` stack) =
  Run (restrict sub' thin) `On`
  stack
step (EvalSub (sub :< t) sub' `On` stack) =
  EvalSub sub sub' `On`
  EvalSnoc1 t sub' :: stack
step (App (Element (Abs t) prf) u `On` stack) =
  Eval t (Element (Base Id :< fst u) (Base :< snd u)) `On`
  stack
step (App (Element t@(Var _) prf) u `On` stack) =
  Run (Element (App t (fst u)) (Ntrl $ App Var (snd u))) `On`
  stack
step (App (Element t@(App _ _) prf) u `On` stack) =
  Run (Element (App t (fst u)) (Ntrl $ App (appNtrl prf) (snd u))) `On`
  stack
step (App (Element t@(Rec _ _ _) prf) u `On` stack) =
  Run (Element (App t (fst u)) (Ntrl $ App (recNtrl prf) (snd u))) `On`
  stack
step (App (Element t@(Sub _ _) prf) u `On` stack) = void $ absurd prf
step (Rec (Element Zero prf) u v `On` stack) =
  Run u `On`
  stack
step (Rec (Element (Succ t) prf) u v `On` stack) =
  Rec (Element t (predNorm prf)) u v `On`
  RecSucc1 v :: stack
step (Rec (Element t@(Var _) prf) u v `On` stack) =
  Run (Element (Rec t (fst u) (fst v)) (Ntrl $ Rec Var (snd u) (snd v))) `On`
  stack
step (Rec (Element t@(App _ _) prf) u v `On` stack) =
  Run (Element (Rec t (fst u) (fst v)) (Ntrl $ Rec (appNtrl prf) (snd u) (snd v))) `On`
  stack
step (Rec (Element t@(Rec _ _ _) prf) u v `On` stack) =
  Run (Element (Rec t (fst u) (fst v)) (Ntrl $ Rec (recNtrl prf) (snd u) (snd v))) `On`
  stack
step (Rec (Element t@(Sub _ _) prf) u v `On` stack) = void $ absurd prf
step (Run sub `On` EvalAbs1 t :: stack) =
  Eval t (Element (fst sub :< Var Here) (snd sub :< Ntrl Var)) `On`
  EvalAbs2 :: stack
step (Run t `On` EvalAbs2 :: stack) =
  Run (Element (Abs $ fst t) (Abs $ snd t)) `On`
  stack
step (Run t `On` EvalApp1 u sub :: stack) =
  Eval u sub `On`
  EvalApp2 t :: stack
step (Run u `On` EvalApp2 t :: stack) =
  App t u `On`
  stack
step (Run t `On` EvalSucc1 :: stack) =
  Run (Element (Succ $ fst t) (Succ $ snd t)) `On`
  stack
step (Run t `On` EvalRec1 u v sub :: stack) =
  Eval u sub `On`
  EvalRec2 t v sub :: stack
step (Run u `On` EvalRec2 t v sub :: stack) =
  EvalSub (fst sub) (Element (Base $ Drop Id) Base) `On`
  EvalRec3 t u v :: stack
step (Run sub `On` EvalRec3 t u v :: stack) =
  Eval v (Element (fst sub :< Var Here) (snd sub :< Ntrl Var)) `On`
  EvalRec4 t u :: stack
step (Run v `On` EvalRec4 t u :: stack) =
  Rec t u v `On`
  stack
step (Run sub `On` EvalSub1 t :: stack) =
  Eval t sub `On`
  stack
step (Run sub `On` EvalSnoc1 t sub' :: stack) =
  Eval t sub' `On`
  EvalSnoc2 sub :: stack
step (Run t `On` EvalSnoc2 sub :: stack) =
  Run (Element (fst sub :< fst t) (snd sub :< snd t)) `On`
  stack
step (Run val `On` RecSucc1 v :: stack) =
  Eval (fst v) (Element (Base Id :< fst val) (Base :< snd val)) `On`
  stack

unwindStack : Raw a -> (stack : Stack a b) -> Raw b
unwindStack x [] = x
unwindStack sub (EvalAbs1 t :: stack) = unwindStack (Abs (Sub t (sub :< Var Here))) stack
unwindStack t (EvalAbs2 :: stack) = unwindStack (Abs t) stack
unwindStack t (EvalApp1 u sub :: stack) = unwindStack (App t (Sub u (fst sub))) stack
unwindStack u (EvalApp2 t :: stack) = unwindStack (App (fst t) u) stack
unwindStack t (EvalSucc1 :: stack) = unwindStack (Succ t) stack
unwindStack t (EvalRec1 u v sub :: stack) =
  unwindStack (Rec t (Sub u (fst sub)) (Sub v (Base (Drop Id) . fst sub :< Var Here))) stack
unwindStack u (EvalRec2 t v sub :: stack) =
  unwindStack (Rec (fst t) u (Sub v (Base (Drop Id) . fst sub :< Var Here))) stack
unwindStack sub (EvalRec3 t u v :: stack) =
  unwindStack (Rec (fst t) (fst u) (Sub v (sub :< Var Here))) stack
unwindStack v (EvalRec4 t u :: stack) =
  unwindStack (Rec (fst t) (fst u) v) stack
unwindStack sub (EvalSub1 t :: stack) = unwindStack (Sub t sub) stack
unwindStack sub (EvalSnoc1 t sub' :: stack) = unwindStack (sub :< Sub t (fst sub')) stack
unwindStack t (EvalSnoc2 sub :: stack) = unwindStack (fst sub :< t) stack
unwindStack val (RecSucc1 v :: stack) = unwindStack (Sub (fst v) (Base Id :< val)) stack

unwind : Config a -> Raw a
unwind (Eval t sub `On` stack) = unwindStack (Sub t $ fst sub) stack
unwind (EvalSub sub sub' `On` stack) = unwindStack (fst sub' . sub) stack
unwind (App t u `On` stack) = unwindStack (App (fst t) (fst u)) stack
unwind (Rec t u v `On` stack) = unwindStack (Rec (fst t) (fst u) (fst v)) stack
unwind (Run x `On` stack) = unwindStack (fst x) stack

eval : Nat -> Config ret -> Raw ret
eval 0 config = unwind config
eval (S n) (Run x `On` []) = fst x
eval (S n) config@(Run _ `On` _ :: _) = eval n (step config)
eval (S n) config@(Eval _ _ `On` _) = eval n (step config)
eval (S n) config@(EvalSub _ _ `On` _) = eval n (step config)
eval (S n) config@(App _ _ `On` _) = eval n (step config)
eval (S n) config@(Rec _ _ _ `On` _) = eval n (step config)
