module Total.Syntax

import public Data.List
import public Data.List.Quantifiers
import public Data.SnocList
import public Data.SnocList.Quantifiers
import public Total.Term
import public Total.Term.CoDebruijn

infixr 20 ~>*
infixl 9 .~, .*

public export
(~>*) : SnocList Ty -> Ty -> Ty
tys ~>* ty = foldr (~>) ty tys

public export
0 Fun : {sx : SnocList a} -> Len sx -> (a -> Type) -> Type -> Type
Fun Z arg ret = ret
Fun (S {x = ty} k) arg ret = Fun k arg (arg ty -> ret)

after : (k : Len sx) -> (a -> b) -> Fun k p a -> Fun k p b
after Z f x = f x
after (S k) f x = after k (f .) x

before :
  (k : Len sx) ->
  (forall x. p x -> q x) ->
  Fun k q ret ->
  Fun k p ret
before Z f x = x
before (S k) f x = before k f (after k (. f) x)

export
lit : Len ctx => Nat -> FullTerm N ctx
lit 0 = Zero `Over` empty
lit (S n) = suc (lit n)

absHelper :
  (k : Len tys) ->
  Fun k (flip Elem (ctx ++ tys)) (FullTerm ty (ctx ++ tys)) ->
  FullTerm (tys ~>* ty) ctx
absHelper Z x = x
absHelper (S k) x =
  absHelper k $
  after k (\f => CoDebruijn.abs (f SnocList.Elem.Here)) $
  before k SnocList.Elem.There x

export
abs' :
  (len : Len ctx) =>
  (k : Len tys) ->
  Fun k (flip FullTerm (ctx ++ tys)) (FullTerm ty (ctx ++ tys)) ->
  FullTerm (tys ~>* ty) ctx
abs' k = absHelper k . before k (var @{lenAppend len k})

export
app' :
  {tys : SnocList Ty} ->
  FullTerm (tys ~>* ty) ctx ->
  All (flip FullTerm ctx) tys ->
  FullTerm ty ctx
app' t [<] = t
app' t (us :< u) = app (app' t us) u

-- export
-- compose :
--   {ty, ty' : Ty} ->
--   (t : FullTerm (ty' ~> ty'') ctx) ->
--   (u : FullTerm (ty ~> ty') ctx) ->
--   Len u.support =>
--   Covering Covers t.thin u.thin ->
--   CoTerm (ty ~> ty'') ctx
-- compose (t `Over` thin1) (u `Over` thin2) cover =
--   Abs
--     (MakeBound
--       (App
--         (MakePair
--           (t `Over` Drop thin1)
--           (App
--             (MakePair
--               (u `Over` Drop id)
--               (Var `Over` Keep empty)
--               (DropKeep (coverIdLeft empty)))
--            `Over` Keep thin2)
--           (DropKeep cover)))
--       (Keep Empty))

-- export
-- (.~) :
--   Len ctx =>
--   {ty, ty' : Ty} ->
--   CoTerm (ty' ~> ty'') ctx ->
--   CoTerm (ty ~> ty') ctx ->
--   CoTerm (ty ~> ty'') ctx
-- t .~ u = compose (t `Over` id) (u `Over` id) (coverIdLeft id)

export
(.) :
  Len ctx =>
  {ty, ty' : Ty} ->
  FullTerm (ty' ~> ty'') ctx ->
  FullTerm (ty ~> ty') ctx ->
  FullTerm (ty ~> ty'') ctx
t . u = abs' (S Z) (\x => app (drop t) (app (drop u) x))

export
(.*) :
  Len ctx =>
  {ty : Ty} ->
  {tys : SnocList Ty} ->
  FullTerm (ty ~> ty') ctx ->
  FullTerm (tys ~>* ty) ctx ->
  FullTerm (tys ~>* ty') ctx
(.*) {tys = [<]} t u = app t u
(.*) {tys = tys :< ty''} t u = abs' (S Z) (\f => drop t . f) .*  u

export
lift : Len ctx => FullTerm ty [<] -> FullTerm ty ctx
lift t = wkn t empty

export
id' : CoTerm (ty ~> ty) [<]
id' = Abs (MakeBound Var (Keep Empty))

export
id : FullTerm (ty ~> ty) [<]
id = id' `Over` empty
