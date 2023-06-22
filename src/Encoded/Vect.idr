module Encoded.Vect

import Data.String

import Encoded.Bool
import Encoded.Pair
import Encoded.Fin

import Term.Syntax

export
Vect : Nat -> Ty -> Ty
Vect k ty = Fin k ~> ty

export
nil : {ty : Ty} -> Term (Vect 0 ty) ctx
nil = absurd

export
cons : {k : Nat} -> {ty : Ty} -> Term (ty ~> Vect k ty ~> Vect (S k) ty) ctx
cons = Abs $ Abs $ Abs $
  let x = Var $ There $ There Here in
  let xs = Var $ There Here in
  let i = Var Here in
  App induct [<i, x, App uncurry [<Abs $ Const $ App (shift xs) (Var Here)]]

export
tabulate : Term ((Fin k ~> ty) ~> Vect k ty) ctx
tabulate = Id

export
dmap :
  {k : Nat} ->
  {ty1, ty2 : Ty} ->
  Term ((Fin k ~> ty1 ~> ty2) ~> Vect k ty1 ~> Vect k ty2) ctx
dmap =
  Abs $ Abs $ Abs $
    let f = Var (There $ There Here) in
    let xs = Var (There Here) in
    let i = Var Here in
    App f [<i, App xs i]

export
map : {k : Nat} -> {ty1, ty2 : Ty} -> Term ((ty1 ~> ty2) ~> Vect k ty1 ~> Vect k ty2) ctx
map = Abs' (\f => App dmap (Const f))

export
index : {k : Nat} -> {ty : Ty} -> Term (Vect k ty ~> Fin k ~> ty) ctx
index = Id

export
foldr : {k : Nat} -> {ty, ty' : Ty} -> Term (ty' ~> (ty ~> ty' ~> ty') ~> Vect k ty ~> ty') ctx
foldr {k = 0} = Abs $ Const $ Const $ Var Here
foldr {k = S k} = Abs $ Abs $ Abs $
  let z = Var (There $ There Here) in
  let c = Var (There Here) in
  let xs = Var Here in
  App c [<App xs [<zero], App foldr [<z, c, xs . suc]]
