module Total.Syntax

import public Data.List
import public Data.List.Quantifiers
import public Data.SnocList
import public Data.SnocList.Quantifiers
import public Total.Term

infixr 20 ~>*
infix 9 .*

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
Lit : Nat -> Term ctx N
Lit 0 = Zero
Lit (S n) = Suc (Lit n)

AbsHelper :
  (k : Len tys) ->
  Fun k (flip Elem (ctx ++ tys)) (Term (ctx ++ tys) ty) ->
  Term ctx (tys ~>* ty)
AbsHelper Z x = x
AbsHelper (S k) x =
  AbsHelper k $
  after k (\f => Term.Abs (f SnocList.Elem.Here)) $
  before k SnocList.Elem.There x

export
Abs' :
  (k : Len tys) ->
  Fun k (Term (ctx ++ tys)) (Term (ctx ++ tys) ty) ->
  Term ctx (tys ~>* ty)
Abs' k = AbsHelper k . before k Var

export
App' : {tys : SnocList Ty} -> Term ctx (tys ~>* ty) -> All (Term ctx) tys -> Term ctx ty
App' t [<] = t
App' t (us :< u) = App (App' t us) u

export
(.) : Len ctx => {ty, ty' : Ty} -> Term ctx (ty' ~> ty'') -> Term ctx (ty ~> ty') -> Term ctx (ty ~> ty'')
t . u = Abs' (S Z) (\x => App (wkn t (Drop id)) (App (wkn u (Drop id)) x))

export
(.*) :
  Len ctx =>
  {ty : Ty} ->
  {tys : SnocList Ty} ->
  Term ctx (ty ~> ty') ->
  Term ctx (tys ~>* ty) ->
  Term ctx (tys ~>* ty')
(.*) {tys = [<]} t u = App t u
(.*) {tys = tys :< ty''} t u = Abs' (S Z) (\f => wkn t (Drop id) . f) .*  u

export
lift : {ctx : SnocList Ty} -> Term [<] ty -> Term ctx ty
lift t = wkn t empty
