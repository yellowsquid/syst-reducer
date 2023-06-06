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
data Len : SnocList Ty -> Type where
  Z : Len [<]
  S : Len tys -> Len (tys :< ty)

%name Len k, m, n

public export
0 Fun : Len tys -> (Ty -> Type) -> Type -> Type
Fun Z arg ret = ret
Fun (S {ty} k) arg ret = Fun k arg (arg ty -> ret)

after : (k : Len tys) -> (a -> b) -> Fun k p a -> Fun k p b
after Z f x = f x
after (S k) f x = after k (f .) x

before :
  (k : Len tys) ->
  (forall ty. p ty -> q ty) ->
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
(.) : {ty, ty' : Ty} -> Term ctx (ty' ~> ty'') -> Term ctx (ty ~> ty') -> Term ctx (ty ~> ty'')
t . u = Abs' (S Z) (\x => App (wkn t (Drop Id)) (App (wkn u (Drop Id)) x))

export
(.*) :
  {ty : Ty} ->
  {tys : SnocList Ty} ->
  Term ctx (ty ~> ty') ->
  Term ctx (tys ~>* ty) ->
  Term ctx (tys ~>* ty')
(.*) {tys = [<]} t u = App t u
(.*) {tys = tys :< ty''} t u = Abs' (S Z) (\f => wkn t (Drop Id) . f) .*  u

export
lift : {ctx : SnocList Ty} -> Term [<] ty -> Term ctx ty
lift t = wkn t (empty ctx)
