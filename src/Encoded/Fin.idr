module Encoded.Fin

import public Data.Nat
import public Data.Vect

import Data.Stream
import Encoded.Arith
import Encoded.Pair
import Term.Syntax

export
Fin : Nat -> Ty
Fin k = N

oldShow : Nat -> String
oldShow = show

export
zero : Term (Fin (S k)) ctx
zero = Zero

export
suc : Term (Fin k ~> Fin (S k)) ctx
suc = Abs' Suc

export
inject : Term (Fin k ~> Fin (S k)) ctx
inject = Id

export
absurd : {ty : Ty} -> Term (Fin 0 ~> ty) ctx
absurd = Arb

export
induct : {ty : Ty} -> Term (Fin (S k) ~> ty ~> (Fin k * ty ~> ty) ~> ty) ctx
induct = rec

export
forget : Term (Fin k ~> N) ctx
forget = Id

export
divmod' : (k : Nat) -> {auto 0 ok : NonZero k} -> Term (N ~> N * Fin k) ctx
divmod' k = Abs' (\n => App pair [<n `div` Op (Lit k), n `mod` Op (Lit k)])
