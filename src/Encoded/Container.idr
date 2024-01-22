module Encoded.Container

import Encoded.Arith
import Encoded.Bool
import Encoded.Fin
import Encoded.Pair
import Encoded.Sum
import Encoded.Vect
import Term.Syntax

%ambiguity_depth 6
%prefix_record_projections off

-- Utilities -------------------------------------------------------------------

gtabulate : {sx : SnocList a} -> ({x : a} -> Elem x sx -> p (f x)) -> All p (map f sx)
gtabulate {sx = [<]} g = [<]
gtabulate {sx = sx :< x} g = gtabulate (g . There) :< g Here

-- Adds a value to the start of a stream
cons : {ty : Ty} -> Term (ty ~> (N ~> ty) ~> (N ~> ty)) ctx
cons = Abs $ Abs $ Abs $
  let x = Var (There $ There Here) in
  let xs = Var (There Here) in
  let n = Var Here in
  App rec [<n, x, xs . fst]

-- Cases -----------------------------------------------------------------------

public export
Case : Type
Case = (Maybe Ty, Nat)

public export
semCase : Case -> Ty -> Ty
semCase (Just tag, k) ty = tag * Vect k ty
semCase (Nothing, k) ty = Vect k ty

unitCase : Case -> Ty
unitCase (Just tag, k) = tag
unitCase (Nothing, k) = N

forgetCase : {c : Case} -> {ty : Ty} -> Term (semCase c ty ~> unitCase c) ctx
forgetCase {c = (Just tag, k)} = fst
forgetCase {c = (Nothing, k)} = Arb

dmapCase :
  {c : Case} ->
  {ty, ty' : Ty} ->
  Term ((Fin (snd c) ~> ty ~> ty') ~> semCase c ty ~> semCase c ty') ctx
dmapCase {c = (Just tag, k)} = Abs' (\f => App (mapSnd . dmap) [<f])
dmapCase {c = (Nothing, k)} = dmap

children : {c : Case} -> {ty : Ty} -> Term (semCase c ty ~> Vect (snd c) ty) ctx
children {c = (Just tag, k)} = snd
children {c = (Nothing, k)} = Id

-- Containers ------------------------------------------------------------------

public export
record Container where
  constructor Cases
  constructors : SnocList Case
  {auto 0 ok : NonEmpty constructors}

%name Container c

public export
sem : Container -> Ty -> Ty
sem c ty = Sum (map (flip semCase ty) c.constructors) @{mapNonEmpty c.ok}

unitSem : Container -> Ty
unitSem c = Sum (map unitCase c.constructors) @{mapNonEmpty c.ok}

-- Fixed Point ----------------------------------------------------------------

export
W : Container -> Ty
W c = (N ~> N * unitSem c * N * N)
--          ^   ^- data     ^   ^- stride
--          +- fuel         +- base

fuelAt : {c : Container} -> Term (W c ~> N ~> N) ctx
fuelAt = Abs' (\c => fst . fst . fst . c)

fuel : {c : Container} -> Term (W c ~> N) ctx
fuel = Abs' (\c => App fuelAt [<c, 0])

vals : {c : Container} -> Term (W c ~> N ~> unitSem c) ctx
vals = Abs' (\c => snd . fst . fst . c)

base : {c : Container} -> Term (W c ~> N ~> N) ctx
base = Abs' (\c => snd . fst . c)

stride : {c : Container} -> Term (W c ~> N ~> N) ctx
stride = Abs' (\c => snd . c)

calcIndex : Term (N ~> N ~> N ~> N) ctx
calcIndex = AbsAll [<_,_,_] (\[<base, stride, n] => base + stride * n)

reroot : {c : Container} -> Term (W c ~> N ~> W c) ctx
reroot = AbsAll [<_,_] (\[<x, n] =>
  App Container.cons
    [<App pair
      [<App pair
      [<App pair
      [<App fuelAt [<x, n]
      , App vals [<x, n]]
      , 1]
      , 1]
    , Abs' (\y =>
        let base' = shift (App base [<x, n]) in
        let stride' = shift (App stride [<x, n]) in
        App
          (Abs' (\z =>
            App pair
            [<App pair
            [<App pair
            [<App fuelAt [<shift (shift x), z]
            , App vals [<shift (shift x), z]]
            , (App base [<shift (shift x), z] `minus` shift base') `div` shift stride']
            , App stride [<shift (shift x), z] `div` shift stride']))
          [<App calcIndex [<base', stride', y]])
    ])

-- Introductor -----------------------------------------------------------------

-- Calculates all fuels for a new W value.
getFuel :
  {cont : Container} ->
  {c : Case} ->
  Term (semCase c (W cont) ~> N ~> N) ctx
getFuel {c = (tag, 0)} =
  -- One tag in total
  Const (Const 1)
getFuel {c = (tag, k@(S _))} =
  Abs' (\x =>
    App Container.cons
      [<App (App foldr [<Zero, Op Plus] . App map [<Abs' Suc . fuel] . children) [<x] -- total fuel
      , Abs'
        (\n =>
          -- fuel (1 + i + k z) => fuel_i (z)
          -- The initial (1 +) is a consequence of the cons.
          let dm = App (divmod' k) [<n] in
          let z = App fst [<dm] in
          let i = App snd [<dm] in
          let child = App (index . children) [<shift x, i] in
          App fuelAt [<child, z]
          )])
  -- App foldr [<Zero, Op Plus] . App map [<Abs' Suc . fuel] . children

-- Calculates all offsets for a new W value.
-- This gives the base and stride for looking up the _children_ of a node.

getBase :
  {cont : Container} ->
  {c : Case} ->
  Term (semCase c (W cont) ~> N ~> N) ctx
getBase {c = (tag, 0)} =
  -- No children, so do not care
  Arb
getBase {c = (tag, k@(S _))} =
  Abs' (\x =>
    App Container.cons
      [<1 -- Children are 1, 2, ..., k
      , Abs'
        (\n =>
          -- base (1 + i + k z) => 1 + i + k (base_i z)
          -- The initial (1 +) is a consequence of the cons.
          let dm = App (divmod' k) [<n] in
          let z = App fst [<dm] in
          let i = App snd [<dm] in
          let child = App (index . children) [<shift x, i] in
          Suc (App forget [<i] + Op (Lit k) * App base [<child, z]))
      ])

getStride :
  {cont : Container} ->
  {c : Case} ->
  Term (semCase c (W cont) ~> N ~> N) ctx
getStride {c = (tag, 0)} =
  -- No children, so do not care
  Arb
getStride {c = (tag, k@(S _))} =
  Abs' (\x =>
    App Container.cons
      [<1 -- Children are 1, 2, ..., k
      , Abs'
        (\n =>
          -- stride (1 + i + k z) => k (stride_i z)
          -- The initial (1 +) is a consequence of the cons.
          let dm = App (divmod' k) [<n] in
          let z = App fst [<dm] in
          let i = App snd [<dm] in
          let child = App (index . children) [<shift x, i] in
          Suc (Op (Lit k) * App base [<child, z]))
          ])

-- Calculates data map for a new W value.
getVals :
  {cont : Container} ->
  {c : Case} ->
  (i : Elem c cont.constructors) ->
  Term (semCase c (W cont) ~> N ~> unitSem cont) ctx
getVals i {c = (tag', 0)} =
  -- Only the root matters.
  Abs' (\x => Const $ App (tag @{mapNonEmpty cont.ok} (elemMap unitCase i) . forgetCase) [<x])
getVals i {c = (tag', k@(S _))} = Abs' (\x =>
  App Container.cons
    [< -- Root is first
      App (tag @{mapNonEmpty cont.ok} (elemMap unitCase i) . forgetCase) [<x]
    , Abs'
      (\n =>
        -- vals (1 + i + k z) => vals_i (z)
        -- The initial (1 +) is a consequence of the cons
        let dm = App (divmod' k) [<n] in
        let z = App fst [<dm] in
        let i = App snd [<dm] in
        let child = App (index . children) [<shift x, i] in
        App vals [<child, z])
    ])

-- Constructs a value for a specific constructor
introCase :
  {cont : Container} ->
  {c : Case} ->
  (i : Elem c cont.constructors) ->
  Term (semCase c (W cont) ~> W cont) ctx
introCase i = AbsAll [<_,_] (\[<x, n] =>
  App pair
  [<App pair
  [<App pair
  [<App getFuel [<x, n]
  , App (getVals i) [<x, n]]
  , App getBase [<x, n]]
  , App getStride [<x, n]])

export
intro : {c : Container} -> Term (sem c (W c) ~> W c) ctx
intro =
  App (any @{mapNonEmpty c.ok}) {sty = map (~> W c) $ map (flip semCase (W c)) c.constructors} $
  rewrite mapFusion (~> W c) (flip semCase (W c)) c.constructors in
  gtabulate introCase

-- Case Splitting --------------------------------------------------------------

fillCase :
  {c : Case} ->
  {ty, ty' : Ty} ->
  Term ((Fin (snd c) ~> ty) ~> (semCase c ty ~> ty') ~> unitCase c ~> ty') ctx
fillCase {c = (Just tag, k)} = Abs $ Abs $ Abs $
  let f = Var (There $ There Here) in
  let sem = Var (There Here) in
  let val = Var Here in
  App sem [<App pair [<val, App tabulate [<f]]]
fillCase {c = (Nothing, k)} =
  Abs $ Abs $ Const $
  let f = Var (There Here) in
  let sem = Var Here in
  App (sem . tabulate) [<f]

elimStep :
  {c : Container} ->
  {ty, ty' : Ty} ->
  Term (map (\c => semCase c ty ~> ty') c.constructors ~>* W c ~> (N ~> ty) ~> (N ~> ty')) ctx
elimStep = AbsAll (_ :< _ :< _ :< _)
  -- fs: update action for each constructor
  -- x : fixed point
  -- f : initial value for each tag
  -- n : tag to compute at
  -- ---
  -- returns updated value for tag
  (\(fs :< x :< f :< n) =>
    let val = App vals [<x, n] in
    let base = App base [<x, n] in
    let stride = App stride [<x, n] in
    App (any @{mapNonEmpty c.ok}) {sty = map (~> ty') (map unitCase c.constructors) :< unitSem c} $
    rewrite mapFusion (~> ty') unitCase c.constructors in
    gtabulate (\i =>
      Syntax.App fillCase
        [<f . App calcIndex [<base, stride] . forget
        , indexAll (elemMap (\c => semCase c ty ~> ty') i) fs
        ]) :<
    val)

export
inspect :
  {c : Container} ->
  {ty : Ty} ->
  Term (map (\c' => semCase c' (W c) ~> ty) c.constructors ~>* W c ~> ty) ctx
inspect = AbsAll (_ :< _) (\(fs :< x) => App elimStep (fs :< x :< App reroot [<x] :< 0))

-- Eliminator ------------------------------------------------------------------

export
elim :
  {c : Container} ->
  {ty : Ty} ->
  Term (map (\c => semCase c ty ~> ty) c.constructors ~>* W c ~> ty) ctx
elim = AbsAll (_ :< _)
  (\(fs :< x) =>
    App
      (Rec (App fuel [<x])
        Arb
        (App elimStep (fs :< x)))
      [<Zero])
