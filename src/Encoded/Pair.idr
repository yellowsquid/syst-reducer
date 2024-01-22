module Encoded.Pair

import Encoded.Bool
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

export
bimap :
  {ty1, ty1', ty2, ty2' : Ty} ->
  Term ((ty1 ~> ty1') ~> (ty2 ~> ty2') ~> ty1 * ty2 ~> ty1' * ty2') ctx
bimap = Abs $ Abs $ Abs $ Abs $
  let f = Var (There $ There $ There Here) in
  let g = Var (There $ There Here) in
  let x = Var (There $ Here) in
  let b = Var Here in
  App if'
    [<b
    , App (inL . f . prL . x) [<True]
    , App (inR . g . prR . x) [<False]
    ]

export
mapFst : {ty1, ty1', ty2 : Ty} -> Term ((ty1 ~> ty1') ~> ty1 * ty2 ~> ty1' * ty2) ctx
mapFst = AbsAll [<_,_] (\[<f, x] =>
  App pair [<App (f . fst) [<x], App snd [<x]])

export
mapSnd : {ty1, ty2, ty2' : Ty} -> Term ((ty2 ~> ty2') ~> ty1 * ty2 ~> ty1 * ty2') ctx
mapSnd = Abs $ Abs $
  let f = Var (There Here) in
  let x = Var Here in
  App pair [<App fst [<x], App (f . snd) [<x]]

export
uncurry : {ty1, ty2, ty : Ty} -> Term ((ty1 ~> ty2 ~> ty) ~> ty1 * ty2 ~> ty) ctx
uncurry = Abs $ Abs $
  let f = Var $ There Here in
  let p = Var Here in
  App f [<App fst [<p], App snd [<p]]
