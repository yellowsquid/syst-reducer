module Thinning

import Data.SnocList.Elem

%prefix_record_projections off

-- Definition ------------------------------------------------------------------

public export
data Thins : SnocList a -> SnocList a -> Type where
  Empty : [<] `Thins` [<]
  Drop : sx `Thins` sy -> sx `Thins` sy :< z
  Keep :
    (thin : sx `Thins` sy) ->
    sx :< z `Thins` sy :< z

%name Thins thin

-- Utility ---------------------------------------------------------------------

public export
data Len : SnocList a -> Type where
  Z : Len [<]
  S : Len sx -> Len (sx :< x)

%name Len k, m, n

%hint
export
length : (sx : SnocList a) -> Len sx
length [<] = Z
length (sx :< x) = S (length sx)

%hint
export
lenSrc : sx `Thins` sy -> Len sx
lenSrc Empty = Z
lenSrc (Drop thin) = lenSrc thin
lenSrc (Keep thin) = S (lenSrc thin)

%hint
export
lenTgt : sx `Thins` sy -> Len sy
lenTgt Empty = Z
lenTgt (Drop thin) = S (lenTgt thin)
lenTgt (Keep thin) = S (lenTgt thin)

%hint
export
lenPred : Len (sx :< x) -> Len sx
lenPred (S k) = k

export
Cast (Len sx) Nat where
  cast Z = 0
  cast (S k) = S (cast k)

-- Smart Constructors ----------------------------------------------------------

export
empty : (len : Len sx) => [<] `Thins` sx
empty {len = Z} = Empty
empty {len = S k} = Drop empty

public export
id : (len : Len sx) => sx `Thins` sx
id {len = Z} = Empty
id {len = S k} = Keep id

export
point : Len sx => Elem ty sx -> [<ty] `Thins` sx
point Here = Keep empty
point (There i) = Drop (point i)

-- Operations ------------------------------------------------------------------

public export
index : sx `Thins` sy -> Elem z sx -> Elem z sy
index (Drop thin) i = There (index thin i)
index (Keep thin) Here = Here
index (Keep thin) (There i) = There (index thin i)

public export
(.) : sy `Thins` sz -> sx `Thins` sy -> sx `Thins` sz
Empty . thin1 = thin1
Drop thin2 . thin1 = Drop (thin2 . thin1)
Keep thin2 . Drop thin1 = Drop (thin2 . thin1)
Keep thin2 . Keep thin1 = Keep (thin2 . thin1)

export
(++) : sx `Thins` sy -> sz `Thins` sw -> sx ++ sz `Thins` sy ++ sw
thin2 ++ Empty = thin2
thin2 ++ (Drop thin1) = Drop (thin2 ++ thin1)
thin2 ++ (Keep thin1) = Keep (thin2 ++ thin1)

-- Commuting Triangles and Coverings -------------------------------------------

data Triangle : sy `Thins` sz -> sx `Thins` sy -> sx `Thins` sz -> Type where
  EmptyAny : Triangle Empty thin1 thin1
  DropAny : Triangle thin2 thin1 thin -> Triangle (Drop thin2) thin1 (Drop thin)
  KeepDrop : Triangle thin2 thin1 thin -> Triangle (Keep thin2) (Drop thin1) (Drop thin)
  KeepKeep : Triangle thin2 thin1 thin -> Triangle (Keep thin2) (Keep thin1) (Keep thin)

data Overlap = Covers | Partitions

namespace Covering
  public export
  data Covering : Overlap -> sx `Thins` sz -> sy `Thins` sz -> Type where
    EmptyEmpty : Covering ov Empty Empty
    DropKeep : Covering ov thin1 thin2 -> Covering ov (Drop thin1) (Keep thin2)
    KeepDrop : Covering ov thin1 thin2 -> Covering ov (Keep thin1) (Drop thin2)
    KeepKeep : Covering Covers thin1 thin2 -> Covering Covers (Keep thin1) (Keep thin2)

record Coproduct {sx, sy, sz : SnocList a} (thin1 : sx `Thins` sz) (thin2 : sy `Thins` sz) where
  constructor MkCoprod
  {0 sw : SnocList a}
  {thin1' : sx `Thins` sw}
  {thin2' : sy `Thins` sw}
  {thin : sw `Thins` sz}
  0 left : Triangle thin thin1' thin1
  0 right : Triangle thin thin2' thin2
  0 cover : Covering Covers thin1' thin2'

coprod : (thin1 : sx `Thins` sz) -> (thin2 : sy `Thins` sz) -> Coproduct thin1 thin2
coprod Empty Empty = MkCoprod EmptyAny EmptyAny EmptyEmpty
coprod (Drop thin1) (Drop thin2) =
  { left $= DropAny, right $= DropAny } (coprod thin1 thin2)
coprod (Drop thin1) (Keep thin2) =
  { left $= KeepDrop, right $= KeepKeep, cover $= DropKeep } (coprod thin1 thin2)
coprod (Keep thin1) (Drop thin2) =
  { left $= KeepKeep, right $= KeepDrop, cover $= KeepDrop } (coprod thin1 thin2)
coprod (Keep thin1) (Keep thin2) =
  { left $= KeepKeep, right $= KeepKeep, cover $= KeepKeep } (coprod thin1 thin2)

-- Splitting off Contexts ------------------------------------------------------

data Split : (global, local : SnocList a) -> (thin : sx `Thins` global ++ local) -> Type where
  MkSplit :
    (thin2 : sx `Thins` global) ->
    (thin1 : used `Thins` local) ->
    Split global local (thin2 ++ thin1)

split : Len local -> (thin : sx `Thins` global ++ local) -> Split global local thin
split Z thin = MkSplit thin Empty
split (S k) (Drop thin) with (split k thin)
  split (S k) (Drop .(thin2 ++ thin1)) | MkSplit thin2 thin1 = MkSplit thin2 (Drop thin1)
split (S k) (Keep thin) with (split k thin)
  split (S k) (Keep .(thin2 ++ thin1)) | MkSplit thin2 thin1 = MkSplit thin2 (Keep thin1)

-- Thinned Things --------------------------------------------------------------

public export
record Thinned (T : SnocList a -> Type) (sx : SnocList a) where
  constructor Over
  {0 support : SnocList a}
  value : T support
  thin : support `Thins` sx

public export
record OverlapPair (overlap : Overlap) (T, U : SnocList a -> Type) (sx : SnocList a) where
  constructor MakePair
  left : Thinned T sx
  right : Thinned U sx
  0 cover : Covering overlap left.thin right.thin

public export
Pair : (T, U : SnocList a -> Type) -> SnocList a -> Type
Pair = OverlapPair Covers

export
MkPair : Thinned t sx -> Thinned u sx -> Thinned (OverlapPair Covers t u) sx
MkPair (t `Over` thin1) (u `Over` thin2) =
  let cp = coprod thin1 thin2 in
  MakePair (t `Over` cp.thin1') (u `Over` cp.thin2') cp.cover `Over` cp.thin

public export
record Binds (local : SnocList a) (T : SnocList a -> Type) (sx : SnocList a) where
  constructor MakeBound
  {0 used : SnocList a}
  value : T (sx ++ used)
  thin : used `Thins` local

export
MkBound : Len local -> Thinned t (sx ++ local) -> Thinned (Binds local t) sx
MkBound k (value `Over` thin) with (split k thin)
  MkBound k (value `Over` .(thin2 ++ thin1)) | MkSplit thin2 thin1 =
    MakeBound value thin1 `Over` thin2

export
map : (forall ctx. t ctx -> u ctx) -> Thinned t ctx -> Thinned u ctx
map f (value `Over` thin) = f value `Over` thin

%hint
export
thinnedLen : Thinned t sx -> Len sx
thinnedLen (value `Over` thin) = lenTgt thin

-- Properties ------------------------------------------------------------------

export
lenUnique : (k, m : Len sx) -> k = m
lenUnique Z Z = Refl
lenUnique (S k) (S m) = cong S (lenUnique k m)

export
identityLeft : (len : Len sy) => (thin : sx `Thins` sy) -> id @{len} . thin = thin
identityLeft {len = Z} thin = Refl
identityLeft {len = S k} (Drop thin) = cong Drop (identityLeft thin)
identityLeft {len = S k} (Keep thin) = cong Keep (identityLeft thin)

export
identityRight : (len : Len sx) => (thin : sx `Thins` sy) -> thin . id @{len} = thin
identityRight {len = Z} Empty = Refl
identityRight (Drop thin) = cong Drop (identityRight thin)
identityRight {len = S k} (Keep thin) = cong Keep (identityRight thin)

export
identitySquared : (len : Len sx) -> id @{len} . id @{len} = id @{len}
identitySquared Z = Refl
identitySquared (S k) = cong Keep (identitySquared k)

export
assoc :
  (thin3 : sz `Thins` sw) ->
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  thin3 . (thin2 . thin1) = (thin3 . thin2) . thin1
assoc Empty thin2 thin1 = Refl
assoc (Drop thin3) thin2 thin1 = cong Drop (assoc thin3 thin2 thin1)
assoc (Keep thin3) (Drop thin2) thin1 = cong Drop (assoc thin3 thin2 thin1)
assoc (Keep thin3) (Keep thin2) (Drop thin1) = cong Drop (assoc thin3 thin2 thin1)
assoc (Keep thin3) (Keep thin2) (Keep thin1) = cong Keep (assoc thin3 thin2 thin1)

export
indexId : (len : Len sx) => (i : Elem x sx) -> index (id @{len}) i = i
indexId {len = S k} Here = Refl
indexId {len = S k} (There i) = cong There (indexId i)

export
indexHomo :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  (i : Elem x sx) ->
  index thin2 (index thin1 i) = index (thin2 . thin1) i
indexHomo Empty Empty i impossible
indexHomo (Drop thin2) thin1 i = cong There (indexHomo thin2 thin1 i)
indexHomo (Keep thin2) (Drop thin1) i = cong There (indexHomo thin2 thin1 i)
indexHomo (Keep thin2) (Keep thin1) Here = Refl
indexHomo (Keep thin2) (Keep thin1) (There i) = cong There (indexHomo thin2 thin1 i)
