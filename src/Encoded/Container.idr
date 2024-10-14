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

-- Entries -----------------------------------------------------------------------

public export
Entry : Type
Entry = (Maybe Ty, Nat)

public export
semEntry : Entry -> Ty -> Ty
semEntry (Just tag, k) ty = tag * Vect k ty
semEntry (Nothing, k) ty = Vect k ty

dmapEntry :
  {c : Entry} ->
  {ty, ty' : Ty} ->
  Term ((Fin (snd c) ~> ty ~> ty') ~> semEntry c ty ~> semEntry c ty') ctx
dmapEntry {c = (Just tag, k)} = Abs' (\f => App (mapSnd . dmap) [<f])
dmapEntry {c = (Nothing, k)} = dmap

mapEntry :
  {c : Entry} ->
  {ty, ty' : Ty} ->
  Term ((ty ~> ty') ~> semEntry c ty ~> semEntry c ty') ctx
mapEntry = dmapEntry . Abs' (\f => Const f)

children : {c : Entry} -> {ty : Ty} -> Term (semEntry c ty ~> Vect (snd c) ty) ctx
children {c = (Just tag, k)} = snd
children {c = (Nothing, k)} = Id

-- Containers ------------------------------------------------------------------

public export
record Container where
  constructor Entries
  constructors : SnocList Entry
  {auto 0 ok : NonEmpty constructors}

%name Container c

public export
sem : Container -> Ty -> Ty
sem c ty = Sum (map (flip semEntry ty) c.constructors) @{mapNonEmpty c.ok}

-- Fixed Point ----------------------------------------------------------------

export
W : Container -> Ty
W c = N * N * (N ~> sem c N)
--    ^   ^- fuel   ^     ^- pointers
--    +- root       +- data

root : {c : Container} -> Term (W c ~> N) ctx
root = fst . fst

fuel : {c : Container} -> Term (W c ~> N) ctx
fuel = snd . fst

heap : {c : Container} -> Term (W c ~> N ~> sem c N) ctx
heap = snd

-- Make the given node the root.
reroot : {c : Container} -> Term (W c ~> N ~> W c) ctx
reroot = AbsAll [<_,_] (\[<x, i] => App mapFst [<App mapFst [<Const i], x])

-- Introductor -----------------------------------------------------------------

-- Calculates all fuels for a new W value.
getFuel :
  {cont : Container} ->
  {c : Entry} ->
  Term (semEntry c (W cont) ~> N) ctx
getFuel {c = (tag, 0)} = Const 1
getFuel {c = (tag, k@(S _))} =
  Abs' (\x => App foldr [<0, max . fuel, App children [<x]])

-- Offset
offset : (k : Nat) -> Term (Fin k ~> N ~> N) ctx
offset k = AbsAll [<_,_] (\[<i, n] => Suc $ App forget [<i] + (Lit k * n))

-- Corrects the index of a child heap.
-- Static argument is the number of heaps being striped.
-- Dynamic argument is the index of this stripe.
fixup :
  {c : Container} ->
  (k : Nat) -> Term (Fin k ~> sem c N ~> sem c N) ctx
fixup k =
  Abs' (\i => Syntax.App (mapAll @{mapNonEmpty c.ok}) (fixEachOne i c.constructors))
  where
  fixEachOne :
    forall ctx.
    Term (Fin k) ctx ->
    (sc : SnocList Entry) ->
    All (\ty => Term ty ctx) (map (\t => t ~> t) $ map (\y => semEntry y N) sc)
  fixEachOne i [<] = [<]
  fixEachOne i (sc :< c) = fixEachOne i sc :< App mapEntry [<App (offset k) [<i]]

-- Calculates data map for a new W value.
getVals :
  {cont : Container} ->
  {c : Entry} ->
  (i : Elem c cont.constructors) ->
  Term (semEntry c (W cont) ~> N ~> sem cont N) ctx
getVals i {c = (tag', 0)} =
  -- Only the root matters.
  AbsAll [<semEntry (tag', 0) (W cont), N]
    (\[<val, _] =>
      App
        ( tag @{mapNonEmpty cont.ok} (elemMap (\y => semEntry y N) i)
        . App mapEntry [<Const Zero])
        [<val] )
getVals i {c = (tag', (S k))} =
  Abs' (\val =>
    App Container.cons
      [< -- Make root first
        App
          ( tag @{mapNonEmpty cont.ok} (elemMap (\y => semEntry y N) i)
          . App dmapEntry [<AbsAll [<Fin (S k), W cont]
              (\[<i, x] => App (offset (S k)) [<i, App root [<x]])])
          [<val]
      , Abs' (\n =>
        -- vals (1 + i + k z) => map (\w => 1 + i + k w) $ vals_i (z)
        -- The initial (1 +) is a consequence of the cons
        let dm = App (divmod' (S k)) [<n] in
        let z = App fst [<dm] in
        let i = App snd [<dm] in
        let child = App (index . children) [<shift val, i] in
        App (fixup (S k)) [<i, App heap [<child, z]])
      ])

-- Constructs a value for a specific constructor
introEntry :
  {cont : Container} ->
  {c : Entry} ->
  (i : Elem c cont.constructors) ->
  Term (semEntry c (W cont) ~> W cont) ctx
introEntry i =
  Abs' (\val => App pair [<App pair
    [<0 -- root
    , App getFuel [<val]]
    , App (getVals i) [<val]])

export
intro : {c : Container} -> Term (sem c (W c) ~> W c) ctx
intro =
  App (any @{mapNonEmpty c.ok}) {sty = map (~> W c) $ map (flip semEntry (W c)) c.constructors} $
  rewrite mapFusion (~> W c) (flip semEntry (W c)) c.constructors in
  gtabulate introEntry

-- Entry Splitting --------------------------------------------------------------

elimStep :
  {c : Container} ->
  {ty, ty' : Ty} ->
  Term
    ( map (\c => semEntry c ty ~> ty') c.constructors ~>*
      (N ~> sem c N) ~>
      (N ~> ty) ~>
      (N ~> ty')
    ) ctx
elimStep = AbsAll (_ :< _ :< _)
  -- fs: update action for each constructor
  -- h : heap
  -- f : initial value for each tag
  -- n : tag to compute at
  -- ---
  -- returns updated value for tag
  (\(fs :< h :< f) =>
    App (any @{mapNonEmpty c.ok}) {sty = map (~> ty') (map (flip semEntry N) c.constructors)}
      (rewrite mapFusion (~> ty') (flip semEntry N) c.constructors in
      gtabulate (\i =>
        indexAll (elemMap (\c => semEntry c ty ~> ty') i) fs .
        App mapEntry [<f]))
    . h)

export
inspect :
  {c : Container} ->
  {ty : Ty} ->
  Term (map (\c' => semEntry c' (W c) ~> ty) c.constructors ~>* W c ~> ty) ctx
inspect = AbsAll (_ :< _) (\(fs :< x) =>
  App elimStep (fs :< App heap [<x] :< App reroot [<x] :< App root [<x]))

-- Eliminator ------------------------------------------------------------------

export
elim :
  {c : Container} ->
  {ty : Ty} ->
  Term (map (\c => semEntry c ty ~> ty) c.constructors ~>* W c ~> ty) ctx
elim = AbsAll (_ :< _)
  (\(fs :< x) =>
    App
      (Rec (App fuel [<x])
        Arb
        (App elimStep (fs :< App heap [<x])))
      [<App root [<x]])
