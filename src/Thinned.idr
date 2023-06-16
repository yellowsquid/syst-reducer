module Thinned

import Control.Order
import Control.Relation

import public Thinning

%prefix_record_projections off

-- Definition ------------------------------------------------------------------

||| Data embedded in a wider context via a thinning.
public export
record Thinned (t : SnocList a -> Type) (sx : SnocList a) where
  constructor Over
  {0 support : SnocList a}
  value : t support
  thin : support `Thins` sx

%name Thinned v, u

||| An equivalence relation on thinned objects.
public export
data (<~>) : Thinned t sx -> Thinned t sx -> Type where
  UpToThin :
    {0 v : t sx} ->
    {0 thin1, thin2 : sx `Thins` sy} ->
    thin1 <~> thin2 ->
    (<~>) {t} (v `Over` thin1) (v `Over` thin2)

%name Thinned.(<~>) prf

export (.supportPrf) :
  {0 v, u : Thinned t sx} ->
  v <~> u ->
  v.support = u.support
(UpToThin prf) .supportPrf = Refl

export (.valuePrf) :
  {0 v, u : Thinned t sx} ->
  (e : v <~> u) ->
  v.value = (rewrite e.supportPrf in u.value)
(UpToThin prf) .valuePrf = Refl

export (.thinPrf) :
  {0 v, u : Thinned t sx} ->
  (e : v <~> u) ->
  v.thin <~> (rewrite e.supportPrf in u.thin)
(UpToThin prf) .thinPrf = prf

--- Properties

export
irrelevantEquiv :
  {0 v, u : Thinned t sx} ->
  (0 prf : v <~> u) ->
  v <~> u
irrelevantEquiv {v = v `Over` thin1, u = u `Over` thin2} prf =
  rewrite prf.supportPrf in
  rewrite prf.valuePrf in
  UpToThin (rewrite sym prf.supportPrf in irrelevantEquiv prf.thinPrf)

export
Reflexive (Thinned t sx) (<~>) where
  reflexive {x = t `Over` thin} = UpToThin reflexive

export
Symmetric (Thinned t sx) (<~>) where
  symmetric (UpToThin prf) = UpToThin (symmetric prf)

export
Transitive (Thinned t sx) (<~>) where
  transitive (UpToThin prf1) (UpToThin prf2) = UpToThin (transitive prf1 prf2)

export
Equivalence (Thinned t sx) (<~>) where

export
Preorder (Thinned t sx) (<~>) where

-- Operations ------------------------------------------------------------------

||| Map the underlying value.
public export
map : (forall sx. t sx -> u sx) -> Thinned t sx -> Thinned u sx
map f (value `Over` thin) = f value `Over` thin

||| Weaken the surrounding context.
public export
wkn : Thinned t sx -> sx `Thins` sy -> Thinned t sy
wkn (value `Over` thin') thin = value `Over` thin . thin'

||| Shift the surrounding context.
public export
shift : Thinned t sx -> Thinned t (sx :< x)
shift (value `Over` thin) = value `Over` Drop thin

--- Properties

export
mapCong :
  {0 t, u : SnocList a -> Type} ->
  (0 f : forall sx. t sx -> u sx) ->
  {0 v1, v2 : Thinned t sx} ->
  v1 <~> v2 ->
  map f v1 <~> map f v2
mapCong f (UpToThin prf) = UpToThin prf

export
shiftCong : {0 v, u : Thinned t sx} -> v <~> u -> shift v <~> shift u
shiftCong (UpToThin prf) = UpToThin (dropCong prf)

-- Pairs -----------------------------------------------------------------------

||| Product of two values ensuring the whole context is used.
public export
record Pair (t, u : SnocList a -> Type) (sx : SnocList a) where
  constructor MakePair
  fst : Thinned t sx
  snd : Thinned u sx
  0 cover : Covering fst.thin snd.thin

||| Smart constructor for thinned pairs.
export
MkPair : Thinned t sx -> Thinned u sx -> Thinned (Pair t u) sx
MkPair (v `Over` thin1) (u `Over` thin2) =
  let cp = coprod thin1 thin2 in
  MakePair (v `Over` cp.thin1') (u `Over` cp.thin2') cp.cover `Over` cp.factor

--- Properties

export
mkPairCong :
  {0 v1, w1 : Thinned t sx} ->
  {0 v2, w2 : Thinned u sx} ->
  v1 <~> w1 ->
  v2 <~> w2 ->
  MkPair v1 v2 <~> MkPair w1 w2
