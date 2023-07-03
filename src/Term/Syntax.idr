module Term.Syntax

import public Data.SnocList
import public Term

%prefix_record_projections off

-- Combinators

export
Id : Term (ty ~> ty) ctx
Id = Abs (Var Here)

export
Arb : {ty : Ty} -> Term ty ctx
Arb {ty = N} = Lit 0
Arb {ty = ty ~> ty'} = Const Arb

export
Zero : Term N ctx
Zero = Lit 0

-- HOAS

infixr 4 ~>*

public export
(~>*) : SnocList Ty -> Ty -> Ty
sty ~>* ty = foldr (~>) ty sty

export
Abs' : (Term ty (ctx :< ty) -> Term ty' (ctx :< ty)) -> Term (ty ~> ty') ctx
Abs' f = Abs (f $ Var Here)

export
App : {sty : SnocList Ty} -> Term (sty ~>* ty) ctx -> All (flip Term ctx) sty -> Term ty ctx
App t [<] = t
App t (us :< u) = App (App t us) u

export
AbsAll :
  (sty : SnocList Ty) ->
  (All (flip Term (ctx ++ sty)) sty -> Term ty (ctx ++ sty)) ->
  Term (sty ~>* ty) ctx
AbsAll [<] f = f [<]
AbsAll (sty :< ty') f = AbsAll sty (\vars => Abs' (\x => f (mapProperty shift vars :< x)))

export
(.) : {ty, ty' : Ty} -> Term (ty' ~> ty'') ctx -> Term (ty ~> ty') ctx -> Term (ty ~> ty'') ctx
t . u = Abs (App (shift t) [<App (shift u) [<Var Here]])

export
(.:) :
  {sty : SnocList Ty} ->
  {ty : Ty} ->
  Term (ty ~> ty') ctx ->
  Term (sty ~>* ty) ctx ->
  Term (sty ~>* ty') ctx
(t .: u) {sty = [<]} = App t u
(t .: u) {sty = sty :< ty''} = Abs' (\f => shift t . f) .: u

-- -- Incomplete Evaluation

-- data IsFunc : FullTerm (ty ~> ty') ctx -> Type where
--   ConstFunc : (t : FullTerm ty' ctx) -> IsFunc (Const t)
--   AbsFunc : (t : FullTerm ty' (ctx :< ty)) -> IsFunc (Abs t)

-- isFunc : (t : FullTerm (ty ~> ty') ctx) -> Maybe (IsFunc t)
-- isFunc Var = Nothing
-- isFunc (Const t) = Just (ConstFunc t)
-- isFunc (Abs t) = Just (AbsFunc t)
-- isFunc (App x) = Nothing
-- isFunc (Rec x) = Nothing

-- app :
--   (ratio : Double) ->
--   {ty : Ty} ->
--   (t : Term (ty ~> ty') ctx) ->
--   {auto 0 ok : IsFunc t.value} ->
--   Term ty ctx ->
--   Maybe (Term ty' ctx)
-- app ratio (Const t `Over` thin) u = Just (t `Over` thin)
-- app ratio (Abs t `Over` thin) u =
--   let uses = countUses (t `Over` Id) Here in
--   let sizeU = size u in
--   if cast (sizeU * uses) <= cast (S (sizeU + uses)) * ratio
--   then
--     Just (subst (t `Over` Keep thin) (Base Id :< u))
--   else
--     Nothing

-- App' :
--   {ty : Ty} ->
--   (ratio : Double) ->
--   Term (ty ~> ty') ctx ->
--   Term ty ctx ->
--   Maybe (Term ty' ctx)
-- App' ratio
--   (Rec (MakePair
--     t
--     (MakePair (u `Over` thin2) (Const v `Over` thin3) _ `Over` thin')
--     _) `Over` thin)
--   arg =
--   case (isFunc u, isFunc v) of
--     (Just ok1, Just ok2) =>
--       let thinA = thin . thin' . thin2 in
--       let thinB = thin . thin' . thin3 in
--       case (app ratio (u `Over` thinA) arg , app ratio (v `Over` thinB) arg)
--       of
--         (Just u, Just v) => Just (Rec (wkn t thin) u (Const v))
--         (Just u, Nothing) => Just (Rec (wkn t thin) u (Const $ App (v `Over` thinB) arg))
--         (Nothing, Just v) => Just (Rec (wkn t thin) (App (u `Over` thinA) arg) (Const v))
--         (Nothing, Nothing) =>
--           Just (Rec (wkn t thin) (App (u `Over` thinA) arg) (Const $ App (v `Over` thinB) arg))
--     _ => Nothing
-- App' ratio t arg =
--   case isFunc t.value of
--     Just _ => app ratio t arg
--     Nothing => Nothing

-- Rec' :
--   {ty : Ty} ->
--   FullTerm N ctx' ->
--   ctx' `Thins` ctx ->
--   Term ty ctx ->
--   Term (ty ~> ty) ctx ->
--   Maybe (Term ty ctx)
-- Rec' (Lit 0) thin u v = Just u
-- Rec' (Lit (S n)) thin u v = Just u
-- Rec' (Suc t) thin u v =
--   let rec = maybe (Rec (t `Over` thin) u v) id (Rec' t thin u v) in
--   Just $ maybe (App v rec) id $ (App' 1 v rec)
-- Rec' t thin (Zero `Over` thin1) (Const Zero `Over` thin2) =
--   Just (Zero `Over` Empty)
-- Rec' t thin u v = Nothing

-- eval' : {ty : Ty} -> (fuel : Nat) -> (ratio : Double) -> Term ty ctx -> (Nat, Term ty ctx)
-- fullEval' : {ty : Ty} -> (fuel : Nat) -> (ratio : Double) -> FullTerm ty ctx -> (Nat, Term ty ctx)

-- eval' fuel r (t `Over` thin) = mapSnd (flip wkn thin) (fullEval' fuel r t)

-- fullEval' 0 r t = (0, t `Over` Id)
-- fullEval' fuel@(S f) r Var = (fuel, Var `Over` Id)
-- fullEval' fuel@(S f) r (Const t) = mapSnd Const (fullEval' fuel r t)
-- fullEval' fuel@(S f) r (Abs t) = mapSnd Abs (fullEval' fuel r t)
-- fullEval' fuel@(S f) r (App (MakePair t u _)) =
--   case App' r t u of
--     Just t => (f, t)
--     Nothing =>
--       let (fuel', t) = eval' f r t in
--       let (fuel', u) = eval' (assert_smaller fuel fuel') r u in
--       (fuel', App t u)
-- fullEval' fuel@(S f) r (Lit n) = (fuel, Lit n `Over` Id)
-- fullEval' fuel@(S f) r (Suc t) = mapSnd Suc (fullEval' fuel r t)
-- fullEval' fuel@(S f) r (Rec (MakePair t (MakePair u v _ `Over` thin) _)) =
--   case Rec' t.value t.thin (wkn u thin) (wkn v thin) of
--     Just t => (f, t)
--     Nothing =>
--       let (fuel', t) = eval' f r t in
--       let (fuel', u) = eval' (assert_smaller fuel fuel') r u in
--       let (fuel', v) = eval' (assert_smaller fuel fuel') r v in
--       (fuel', Rec t (wkn u thin) (wkn v thin))

-- export
-- eval :
--   {ty : Ty} ->
--   {default 1.5 ratio : Double} ->
--   {default 20000 fuel : Nat} ->
--   Term ty ctx ->
--   Term ty ctx
-- eval t = loop fuel t
--   where
--   loop : Nat -> Term ty ctx -> Term ty ctx
--   loop fuel t =
--     case eval' fuel ratio t of
--       (0, t) => t
--       (S f, t) => loop (assert_smaller fuel f) t
