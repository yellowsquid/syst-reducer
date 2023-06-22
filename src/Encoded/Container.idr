module Encoded.Container

import Encoded.Arith
import Encoded.Bool
import Encoded.Fin
import Encoded.Pair
import Encoded.Sum
import Encoded.Vect
import Term.Syntax

%ambiguity_depth 4
%prefix_record_projections off

public export
Case : Type
Case = (Maybe Ty, Nat)

public export
record Container where
  constructor Cases
  constructors : SnocList Case
  {auto 0 ok : NonEmpty constructors}

%name Container c

public export
semCase : Case -> Ty -> Ty
semCase (Just tag, k) ty = tag * Vect k ty
semCase (Nothing, k) ty = Vect k ty

public export
sem : Container -> Ty -> Ty
sem c ty = Sum (map (flip semCase ty) c.constructors) @{mapNonEmpty c.ok}

unitCase : Case -> Ty
unitCase (Just tag, k) = tag
unitCase (Nothing, k) = N

unitSem : Container -> Ty
unitSem c = Sum (map unitCase c.constructors) @{mapNonEmpty c.ok}

dmapCase :
  {c : Case} ->
  {ty, ty' : Ty} ->
  Term ((Fin (snd c) ~> ty ~> ty') ~> semCase c ty ~> semCase c ty') ctx
dmapCase {c = (Just tag, k)} = Abs' (\f => App (mapSnd . dmap) [<f])
dmapCase {c = (Nothing, k)} = dmap

forgetCase : {c : Case} -> {ty : Ty} -> Term (semCase c ty ~> unitCase c) ctx
forgetCase {c = (Just tag, k)} = fst
forgetCase {c = (Nothing, k)} = Arb

recurse : {c : Case} -> {ty : Ty} -> Term (semCase c ty ~> Vect (snd c) ty) ctx
recurse {c = (Just tag, k)} = snd
recurse {c = (Nothing, k)} = Id

export
W : Container -> Ty
W c = N * (N ~> N * N) * (N ~> unitSem c)
--    ^   ^              ^- data
--    |   + index mapping function: each index has a different base and stride
--    +- pred(fuel) for induction

fuel : {c : Container} -> Term (W c ~> N) ctx
fuel = fst . fst

offset : {c : Container} -> Term (W c ~> N ~> N * N) ctx
offset = snd . fst

vals : {c : Container} -> Term (W c ~> N ~> unitSem c) ctx
vals = snd

-- Adds a value to the start of a stream
cons : {ty : Ty} -> Term (ty ~> (N ~> ty) ~> (N ~> ty)) ctx
cons = Abs $ Abs $ Abs $
  let x = Var (There $ There Here) in
  let xs = Var (There Here) in
  let n = Var Here in
  App rec [<n, x, xs . fst]

-- Calculates total fuel for a new W value.
getFuel :
  {cont : Container} ->
  {c : Case} ->
  Term (semCase c (W cont) ~> N) ctx
getFuel {c = (tag, k)} = App foldr [<Zero, plus] . App map [<Abs' Suc . fuel] . recurse

-- Updates the base and stride for a single recursive position.
-- These are multiplexed later.
stepOffset : {k : Nat} -> Term (Fin k ~> (N ~> N * N) ~> (N ~> N * N)) ctx
stepOffset = Abs $ Abs $ Abs $
  let i = Var (There $ There Here) in
  let f = Var (There Here) in
  let x = Var Here in
  App bimap
    -- Suc is for the initial tag
    [<App (plus . forget . suc) [<i] . App mult [<Lit k]
    , App mult [<Lit k]
    , App f [<x]
    ]

-- Calculates all offsets for a new W value.
getOffset :
  {cont : Container} ->
  {c : Case} ->
  Term (semCase c (W cont) ~> N ~> N * N) ctx
getOffset {c = (tag, 0)} = Const $ Const $ App pair [<Lit 1, Zero]
getOffset {c = (tag, k@(S _))} = Abs' (\x =>
  App cons
    [<App pair [<Lit 1, Zero]
    , Abs' (\n =>
      let dm = App (divmod' k) [<n] in
      let div = App fst [<dm] in
      let mod = App snd [<dm] in
      App stepOffset [<mod, App offset [<App (index . recurse) [<shift x, mod]], div])
    ])

-- Calculates data map for a new W value.
getVals :
  {cont : Container} ->
  {c : Case} ->
  (i : Elem c cont.constructors) ->
  Term (semCase c (W cont) ~> N ~> unitSem cont) ctx
getVals i {c = (tag', 0)} =
  Abs' (\x => Const $ App (tag @{mapNonEmpty cont.ok} (elemMap unitCase i) . forgetCase) [<x])
getVals i {c = (tag', k@(S _))} = Abs' (\x =>
  App Container.cons
    [<App (tag @{mapNonEmpty cont.ok} (elemMap unitCase i) . forgetCase) [<x]
    , Abs' (\n =>
      let dm = App (divmod' k) [<n] in
      let div = App fst [<dm] in
      let mod = App snd [<dm] in
      App vals [<App (index . recurse) [<shift x, mod], div])
    ])

-- Constructs a value for a specific constructor
introCase :
  {cont : Container} ->
  {c : Case} ->
  (i : Elem c cont.constructors) ->
  Term (semCase c (W cont) ~> W cont) ctx
introCase i = Abs' (\x =>
  App pair [<App pair [<App getFuel [<x], App getOffset [<x]], App (getVals i) [<x]])

gtabulate : {sx : SnocList a} -> ({x : a} -> Elem x sx -> p (f x)) -> All p (map f sx)
gtabulate {sx = [<]} g = [<]
gtabulate {sx = sx :< x} g = gtabulate (g . There) :< g Here

export
intro : {c : Container} -> Term (sem c (W c) ~> W c) ctx
intro =
  App (any @{mapNonEmpty c.ok}) {sty = map (~> W c) $ map (flip semCase (W c)) c.constructors} $
  rewrite mapFusion (~> W c) (flip semCase (W c)) c.constructors in
  gtabulate introCase

calcIndex : Term (N * N ~> N ~> N) ctx
calcIndex = Abs' (\bs => App (plus . fst) [<bs] . App (mult . snd) [<bs])

fillCase :
  {c : Case} ->
  {ty : Ty} ->
  Term ((Fin (snd c) ~> ty) ~> (semCase c ty ~> ty) ~> unitCase c ~> ty) ctx
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
  {ty : Ty} ->
  Term
    (map (\c => semCase c ty ~> ty) c.constructors ~>*
     (N ~> N * N) ~>
     (N ~> unitSem c) ~>
     (N ~> ty) ~>
     (N ~> ty))
    ctx
elimStep = AbsAll (_ :< _ :< _ :< _ :< _)
  (\(fs :< offsets :< vals :< rec :< n) =>
    let val = App vals [<n] in
    let offset = App offsets [<n] in
    App (any @{mapNonEmpty c.ok}) {sty = map (~> ty) (map unitCase c.constructors) :< unitSem c} $
    rewrite mapFusion (~> ty) unitCase c.constructors in
    gtabulate (\i =>
      Syntax.App fillCase
        [<rec . App calcIndex [<offset] . forget
        , indexAll (elemMap (\c => semCase c ty ~> ty) i) fs
        ]) :<
    val)

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
        (App elimStep (fs :< App offset [<x] :< App vals [<x])))
      [<Zero])
