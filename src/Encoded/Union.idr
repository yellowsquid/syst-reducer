module Encoded.Union

import Term.Syntax

export
(<+>) : Ty -> Ty -> Ty
N <+> N = N
N <+> (ty2 ~> ty2') = ty2 ~> (N <+> ty2')
(ty1 ~> ty1') <+> N = ty1 ~> (ty1' <+> N)
(ty1 ~> ty1') <+> (ty2 ~> ty2') = (ty1 <+> ty2) ~> (ty1' <+> ty2')

export
swap : {ty1, ty2 : Ty} -> Term ((ty1 <+> ty2) ~> (ty2 <+> ty1)) ctx
swap {ty1 = N, ty2 = N} = Id
swap {ty1 = N, ty2 = ty2 ~> ty2'} = Abs' (\f => swap . f)
swap {ty1 = ty1 ~> ty1', ty2 = N} = Abs' (\f => swap . f)
swap {ty1 = ty1 ~> ty1', ty2 = ty2 ~> ty2'} = Abs' (\f => swap . f . swap)

export
inL : {ty1, ty2 : Ty} -> Term (ty1 ~> (ty1 <+> ty2)) ctx
export
prL : {ty1, ty2 : Ty} -> Term ((ty1 <+> ty2) ~> ty1) ctx

inL {ty1 = N, ty2 = N} = Id
inL {ty1 = N, ty2 = ty2 ~> ty2'} = Abs' (\n => Const (App inL [<n]))
inL {ty1 = ty1 ~> ty1', ty2 = N} = Abs' (\f => inL . f)
inL {ty1 = ty1 ~> ty1', ty2 = ty2 ~> ty2'} = Abs' (\f => inL . f . prL)

prL {ty1 = N, ty2 = N} = Id
prL {ty1 = N, ty2 = ty2 ~> ty2'} = Abs' (\t => App prL [<App t [<Arb]])
prL {ty1 = ty1 ~> ty1', ty2 = N} = Abs' (\t => prL . t)
prL {ty1 = ty1 ~> ty1', ty2 = ty2 ~> ty2'} = Abs' (\t => prL . t . inL)

export
inR : {ty1, ty2 : Ty} -> Term (ty2 ~> (ty1 <+> ty2)) ctx
inR = swap . inL

export
prR : {ty1, ty2 : Ty} -> Term ((ty1 <+> ty2) ~> ty2) ctx
prR = prL . swap
