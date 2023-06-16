module Encoded.Pair

import Encoded.Bool
import Encoded.Union
import Term.Syntax

export
(*) : Ty -> Ty -> Ty
ty1 * ty2 = B ~> (ty1 <+> ty2)

export
pair : {ty1, ty2 : Ty} -> Term (ty1 ~> ty2 ~> (ty1 * ty2)) ctx
pair = Abs $ Abs $ Abs $
  let t = Var (There $ There Here) in
  let u = Var (There Here) in
  let b = Var Here in
  App if' [<b, App inL [<t], App inR [<u]]

export
fst : {ty1, ty2 : Ty} -> Term ((ty1 * ty2) ~> ty1) ctx
fst = Abs $ App (prL . Var Here) [<True]

export
snd : {ty1, ty2 : Ty} -> Term ((ty1 * ty2) ~> ty2) ctx
snd = Abs $ App (prR . Var Here) [<False]
