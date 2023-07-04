module Encoded.Sum

import public Data.SnocList.Operations

import Encoded.Bool
import Encoded.Pair
import Term.Syntax

-- Binary Sums -----------------------------------------------------------------

export
(+) : Ty -> Ty -> Ty
ty1 + ty2 = B * (ty1 <+> ty2)

export
left : {ty1, ty2 : Ty} -> Term (ty1 ~> (ty1 + ty2)) ctx
left = Abs' (\t => App pair [<True, App inL [<t]])

export
right : {ty1, ty2 : Ty} -> Term (ty2 ~> (ty1 + ty2)) ctx
right = Abs' (\t => App pair [<False, App inR [<t]])

export
case' : {ty1, ty2, ty : Ty} -> Term ((ty1 + ty2) ~> (ty1 ~> ty) ~> (ty2 ~> ty) ~> ty) ctx
case' = Abs' (\t =>
  App if'
    [<App fst [<t]
    , Abs $ Const $ App (Var Here . prL . snd) [<shift t]
    , Const $ Abs $ App (Var Here . prR . snd) [<shift t]
    ])

export
either : {ty1, ty2, ty : Ty} -> Term ((ty1 ~> ty) ~> (ty2 ~> ty) ~> (ty1 + ty2) ~> ty) ctx
either = Abs $ Abs $ Abs $
  let f = Var $ There $ There Here in
  let g = Var $ There Here in
  let x = Var Here in
  App case' [<x, f, g]

-- N-ary Sums ------------------------------------------------------------------

public export
mapNonEmpty : NonEmpty sx -> NonEmpty (map f sx)
mapNonEmpty IsSnoc = IsSnoc

export
Sum : (sty : SnocList Ty) -> {auto 0 ok : NonEmpty sty} -> Ty
Sum [<ty] = ty
Sum (sty@(_ :< _) :< ty) = Sum sty + ty

export
any :
  {sty : SnocList Ty} ->
  {ty : Ty} ->
  {auto 0 ok : NonEmpty sty} ->
  Term (map (~> ty) sty ~>* Sum sty ~> ty) ctx
any {sty = [<ty']} = Id
any {sty = sty :< ty'' :< ty'} =
  Abs (Abs $ Abs $
    let rec = Var (There $ There Here) in
    let f = Var (There Here) in
    let g = Var Here in
    App either [<App rec [<f], g]) .:
  any {sty = sty :< ty''}

export
tag :
  {sty : SnocList Ty} ->
  {ty : Ty} ->
  {auto 0 ok : NonEmpty sty} ->
  Elem ty sty ->
  Term (ty ~> Sum sty) ctx
tag {sty = [<ty]} Here = Id
tag {sty = sty :< ty' :< ty} Here = right
tag {sty = sty :< ty'' :< ty'} (There i) = left . tag i
