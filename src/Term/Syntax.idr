module Term.Syntax

import public Data.SnocList
import public Term

-- Combinators

export
Id : Term (ty ~> ty) ctx
Id = Abs (Var Here)

export
Arb : {ty : Ty} -> Term ty ctx
Arb {ty = N} = Zero
Arb {ty = ty ~> ty'} = Const Arb

export
Lit : Nat -> Term N ctx
Lit 0 = Zero
Lit (S k) = Suc (Lit k)

-- HOAS

infix 4 ~>*

public export
(~>*) : SnocList Ty -> Ty -> Ty
sty ~>* ty = foldr (~>) ty sty

export
Abs' : (Term ty (ctx :< ty) -> Term ty' (ctx :< ty)) -> Term (ty ~> ty') ctx
Abs' f = Abs (f $ Var Here)

export
App' : {ty : Ty} -> Term (ty ~> ty') ctx -> Term ty ctx -> Term ty' ctx
App' (Const t `Over` thin) u = t `Over` thin
App' (Abs t `Over` thin) u = subst (t `Over` Keep thin) (Base Id :< u)
App' t u = App t u

export
App : {sty : SnocList Ty} -> Term (sty ~>* ty) ctx -> All (flip Term ctx) sty -> Term ty ctx
App t [<] = t
App t (us :< u) = App' (App t us) u

export
(.) : {ty, ty' : Ty} -> Term (ty' ~> ty'') ctx -> Term (ty ~> ty') ctx -> Term (ty ~> ty'') ctx
t . u = Abs (App (shift t) [<App (shift u) [<Var Here]])
