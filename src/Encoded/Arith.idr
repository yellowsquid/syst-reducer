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
plus : Term (N ~> N ~> N) ctx
plus = Abs' (\n => Rec n Id (Abs' (Abs' Suc .)))

export
pred : Term (N ~> N) ctx
-- pred = Abs' (\n => App rec [<n, Zero, fst])
pred = Abs'
  (\n => App
    (Rec n
      (Const Zero)
      (Abs $ Abs $
        let f = Var (There Here) in
        let k = Var Here in
        Rec k
          (Lit 1)
          (Const $
            Rec (App f [<Zero])
              Zero
              (Const $ Suc $ App f [<Lit 1]))))
    [<Lit 1])

export
minus : Term (N ~> N ~> N) ctx
minus = Abs $ Abs $
  let m = Var $ There Here in
  let n = Var Here in
  Rec n m pred

export
mult : Term (N ~> N ~> N) ctx
mult = Abs' (\n =>
  Rec n
    (Const Zero)
    (Abs $ Abs $
      let f = Var $ There Here in
      let m = Var Here in
      App plus [<m, App f [<m]]))

export
lte : Term (N ~> N ~> B) ctx
lte = Abs' (\m => isZero . App minus [<m])

export
equal : Term (N ~> N ~> B) ctx
equal = Abs $ Abs $
  let m = Var $ There Here in
  let n = Var Here in
  App and [<App lte [<m, n], App lte [<n, m]]

export
divmod : Term (N ~> N ~> N * N) ctx
divmod = Abs $ Abs $
  let n = Var (There Here) in
  let d = Var Here in
  Rec
    n
    (App pair [<Zero, Zero])
    (Abs' (\p =>
      App if'
        [<App lte [<shift d, Suc (App snd [<p])]
        , App pair [<Suc (App fst [<p]), Zero]
        , App mapSnd [<Abs' Suc, p]]))
