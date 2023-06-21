module Encoded.Sum

import public Data.List
import public Data.List.Elem
import public Data.List.Quantifiers

import Encoded.Bool
import Encoded.Pair
import Encoded.Union
import Term.Semantics
import Term.Syntax

-- Binary Sums -----------------------------------------------------------------

export
(+) : Ty -> Ty -> Ty
ty1 + ty2 = B * (ty1 <+> ty2)

export
{ty1, ty2 : Ty} -> Show (TypeOf ty1) => Show (TypeOf ty2) => Show (TypeOf (ty1 + ty2)) where
  show p =
    if toBool (sem fst [<] p)
    then fastConcat ["Left (", show (sem (prL . snd) [<] p), ")"]
    else fastConcat ["Right (", show (sem (prR . snd) [<] p), ")"]

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
mapNonEmpty : NonEmpty xs -> NonEmpty (map f xs)
mapNonEmpty IsNonEmpty = IsNonEmpty

export
Sum : (tys : List Ty) -> {auto 0 ok : NonEmpty tys} -> Ty
Sum = foldr1 (+)

export
any :
  {tys : List Ty} ->
  {ty : Ty} ->
  {auto 0 ok : NonEmpty tys} ->
  All (\ty' => Term (ty' ~> ty) ctx) tys ->
  Term (Sum tys ~> ty) ctx
any [f] = f
any (f :: fs@(_ :: _)) = App either [<f, any fs]

export
tag :
  {tys : List Ty} ->
  {ty : Ty} ->
  {auto 0 ok : NonEmpty tys} ->
  Elem ty tys ->
  Term (ty ~> Sum tys) ctx
tag {tys = [_]} Here = Id
tag {tys = _ :: _ :: _} Here = left
tag {tys = _ :: _ :: _} (There i) = right . tag i
