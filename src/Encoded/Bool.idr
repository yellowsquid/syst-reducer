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
