module Encoded.Bool

import Term.Syntax

export
B : Ty
B = N

export
True : Term B ctx
True = Lit 0
  
export
False : Term B ctx
False = Lit 1

export
if' : Term (B ~> ty ~> ty ~> ty) ctx
if' = Abs' (\b =>
  Rec b
    (Abs $ Const $ Var Here)
    (Const $ Const $ Abs $ Var Here))

export
and : Term (B ~> B ~> B) ctx
and = Abs' (\b => App if' [<b, Id, Const False])

export
or : Term (B ~> B ~> B) ctx
or = Abs' (\b => App if' [<b, Const True, Id])

export
not : Term (B ~> B) ctx
not = Abs' (\b => App if' [<b, False, True])

export
isZero : Term (N ~> B) ctx
isZero = Id
