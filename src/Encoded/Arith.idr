module Encoded.Arith

import Encoded.Bool
import Encoded.Pair
import Term.Syntax

export
rec : {ty : Ty} -> Term (N ~> ty ~> (N * ty ~> ty) ~> ty) ctx
rec = Abs $ Abs $ Abs $
  let n = Var $ There $ There Here in
  let z = Var $ There Here in
  let s = Var Here in
  let 
    p : Term (N * ty) (ctx :< N :< ty :< (N * ty ~> ty))
    p = Rec n
      (App pair [<Zero, z])
      (Abs' (\p =>
        App pair
          [<Suc (App fst [<p])
          , App (shift s) [<p]]))
  in
  App snd [<p]

export
lte : Term (N ~> N ~> B) ctx
lte = Abs' (\m => isZero . App (Op Minus) [<m])

export
equal : Term (N ~> N ~> B) ctx
equal = Abs $ Abs $
  let m = Var $ There Here in
  let n = Var Here in
  and (App lte [<m, n]) (App lte [<n, m])

export
max : Term (N ~> N ~> N) ctx
max = AbsAll [<N, N] (\[<x, y] => x + (y `minus` x))
