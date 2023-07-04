module Term.Syntax

import public Data.SnocList
import public Term

%prefix_record_projections off

-- Combinators

export
Id : Term (ty ~> ty) ctx
Id = Abs (Var Here)

export
Zero : Term N ctx
Zero = Op (Lit 0)

export
Suc : Term N ctx -> Term N ctx
Suc t = App (Op Suc) t

export
Num (Term N ctx) where
  t + u = App (App (Op Plus) t) u
  t * u = App (App (Op Mult) t) u
  fromInteger = Op . Lit . fromInteger

export
pred : Term N ctx -> Term N ctx
pred t = App (Op Pred) t

export
minus : Term N ctx -> Term N ctx -> Term N ctx
t `minus` u = App (App (Op Minus) t) u

export
div : Term N ctx -> Term N ctx -> Term N ctx
t `div` u = App (App (Op Div) t) u

export
mod : Term N ctx -> Term N ctx -> Term N ctx
t `mod` u = App (App (Op Mod) t) u

export
Arb : {ty : Ty} -> Term ty ctx
Arb {ty = N} = Zero
Arb {ty = ty ~> ty'} = Const Arb

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
