module Encoded.Union

import Term.Syntax

export
(<+>) : Ty -> Ty -> Ty
N <+> N = N
N <+> (ty2 ~> ty2') = ty2 ~> (N <+> ty2')
(ty1 ~> ty1') <+> N = ty1 ~> (ty1' <+> N)
(ty1 ~> ty1') <+> (ty2 ~> ty2') = (ty1 <+> ty2) ~> (ty1' <+> ty2')

export
inL : {ty1, ty2 : Ty} -> Term (ty1 ~> (ty1 <+> ty2)) ctx
export
prL : {ty1, ty2 : Ty} -> Term ((ty1 <+> ty2) ~> ty1) ctx

inL {ty1 = N, ty2 = N} = Id
inL {ty1 = N, ty2 = _ ~> _} = AbsAll [<_,_] (\[<x, _] => App inL [<x])
inL {ty1 = _ ~> _, ty2 = N} = Abs' (\f => inL . f)
inL {ty1 = _ ~> _, ty2 = _ ~> _} = Abs' (\f => inL . f . prL)

prL {ty1 = N, ty2 = N} = Id
prL {ty1 = N, ty2 = _ ~> _} = Abs' (\f => App (prL . f) [<Arb])
prL {ty1 = _ ~> _, ty2 = N} = Abs' (\f => prL . f)
prL {ty1 = _ ~> _, ty2 = _ ~> _} = Abs' (\f => prL . f . inL)

export
inR : {ty1, ty2 : Ty} -> Term (ty2 ~> (ty1 <+> ty2)) ctx
export
prR : {ty1, ty2 : Ty} -> Term ((ty1 <+> ty2) ~> ty2) ctx

inR {ty1 = N, ty2 = N} = Id
inR {ty1 = N, ty2 = _ ~> _} = Abs' (\f => inR . f)
inR {ty1 = _ ~> _, ty2 = N} = AbsAll [<_,_] (\[<x, _] => App inR [<x])
inR {ty1 = _ ~> _, ty2 = _ ~> _} = Abs' (\f => inR . f . prR)

prR {ty1 = N, ty2 = N} = Id
prR {ty1 = N, ty2 = _ ~> _} = Abs' (\f => prR . f)
prR {ty1 = _ ~> _, ty2 = N} = Abs' (\f => App (prR . f) [<Arb])
prR {ty1 = _ ~> _, ty2 = _ ~> _} = Abs' (\f => prR . f . inR)
