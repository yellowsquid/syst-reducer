module Encoded.Bool

import Term.Syntax

export
B : Ty
B = N

export
True : Term B ctx
True = 0
  
export
False : Term B ctx
False = 1

export
if' : {ty : Ty} -> Term B ctx -> Term ty ctx -> Term ty ctx -> Term ty ctx
if' b t f = Rec b t (Const f)

export
and : Term B ctx -> Term B ctx -> Term B ctx
and b1 b2 = if' b1 b2 False

export
or : Term B ctx -> Term B ctx -> Term B ctx
or b1 b2 = if' b1 True b2

export
not : Term (B ~> B) ctx
not = Abs' (\b => if' b False True)

export
isZero : Term (N ~> B) ctx
isZero = Id
