module Thinning

import Data.SnocList.Elem

-- Definition ------------------------------------------------------------------

public export
data Thins : SnocList a -> SnocList a -> Type
public export
data NotId : Thins sx sy -> Type

data Thins where
  Id : sx `Thins` sx
  Drop : sx `Thins` sy -> sx `Thins` sy :< z
  Keep :
    (thin : sx `Thins` sy) ->
    {auto 0 prf : NotId thin} ->
    sx :< z `Thins` sy :< z

data NotId where
  DropNotId : NotId (Drop thin)
  KeepNotId : (0 prf : NotId thin) -> NotId (Keep thin)

%name Thins thin

-- Smart Constructors ----------------------------------------------------------

public export
keep : sx `Thins` sy -> sx :< z `Thins` sy :< z
keep Id = Id
keep (Drop thin) = Keep (Drop thin)
keep (Keep thin) = Keep (Keep thin)

-- Operations ------------------------------------------------------------------

public export
index : sx `Thins` sy -> Elem z sx -> Elem z sy
index Id i = i
index (Drop thin) i = There (index thin i)
index (Keep thin) Here = Here
index (Keep thin) (There i) = There (index thin i)

public export
(.) : sy `Thins` sz -> sx `Thins` sy -> sx `Thins` sz
compNotId :
  {0 thin2 : sy `Thins` sz} ->
  {0 thin1 : sx `Thins` sy} ->
  NotId thin2 -> NotId thin1 ->
  NotId (thin2 . thin1)

Id . thin1 = thin1
(Drop thin2) . thin1 = Drop (thin2 . thin1)
(Keep thin2) . Id = Keep thin2
(Keep thin2) . (Drop thin1) = Drop (thin2 . thin1)
(Keep {prf = prf2} thin2) . (Keep {prf = prf1} thin1) =
  Keep {prf = compNotId prf2 prf1} (thin2 . thin1)

compNotId DropNotId p = DropNotId
compNotId (KeepNotId prf) DropNotId = DropNotId
compNotId (KeepNotId prf) (KeepNotId prf') = KeepNotId (compNotId prf prf')

-- Properties ------------------------------------------------------------------

-- NotId

NotIdUnique : (p, q : NotId thin) -> p = q
NotIdUnique DropNotId DropNotId = Refl
NotIdUnique (KeepNotId prf) (KeepNotId prf) = Refl

-- index

export
indexKeepHere : (thin : sx `Thins` sy) -> index (keep thin) Here = Here
indexKeepHere Id = Refl
indexKeepHere (Drop thin) = Refl
indexKeepHere (Keep thin) = Refl

export
indexKeepThere :
  (thin : sx `Thins` sy) ->
  (i : Elem x sx) ->
  index (keep thin) (There i) = There (index thin i)
indexKeepThere Id i = Refl
indexKeepThere (Drop thin) i = Refl
indexKeepThere (Keep thin) i = Refl

-- (.)

export
assoc :
  (thin3 : ctx'' `Thins` ctx''') ->
  (thin2 : ctx' `Thins` ctx'') ->
  (thin1 : ctx `Thins` ctx') ->
  thin3 . (thin2 . thin1) = (thin3 . thin2) . thin1
assoc Id thin2 thin1 = Refl
assoc (Drop thin3) thin2 thin1 = cong Drop (assoc thin3 thin2 thin1)
assoc (Keep thin3) Id thin1 = Refl
assoc (Keep thin3) (Drop thin2) thin1 = cong Drop (assoc thin3 thin2 thin1)
assoc (Keep thin3) (Keep thin2) Id = Refl
assoc (Keep thin3) (Keep thin2) (Drop thin1) = cong Drop (assoc thin3 thin2 thin1)
assoc (Keep {prf = prf3} thin3) (Keep {prf = prf2} thin2) (Keep {prf = prf1} thin1) =
  let
    eq : (thin3 . (thin2 . thin1) = (thin3 . thin2) . thin1)
    eq = assoc thin3 thin2 thin1
    0 prf :
      (compNotId prf3 (compNotId prf2 prf1) =
       (rewrite eq in compNotId (compNotId prf3 prf2) prf1))
    prf = NotIdUnique _ _
  in
  rewrite eq in
  rewrite prf in
  Refl

export
identityRight : (thin : sx `Thins` sy) -> thin . Id = thin
identityRight Id = Refl
identityRight (Drop thin) = cong Drop (identityRight thin)
identityRight (Keep thin) = Refl

export
indexHomo :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  (i : Elem x sx) ->
  index thin2 (index thin1 i) = index (thin2 . thin1) i
indexHomo Id thin1 i = Refl
indexHomo (Drop thin2) thin1 i = cong There $ indexHomo thin2 thin1 i
indexHomo (Keep thin2) Id i = Refl
indexHomo (Keep thin2) (Drop thin1) i = cong There $ indexHomo thin2 thin1 i
indexHomo (Keep thin2) (Keep thin1) Here = Refl
indexHomo (Keep thin2) (Keep thin1) (There i) = cong There $ indexHomo thin2 thin1 i

export
keepHomo :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  keep thin2 . keep thin1 = keep (thin2 . thin1)
keepHomo Id thin1 = Refl
keepHomo (Drop thin2) Id = rewrite identityRight thin2 in Refl
keepHomo (Drop thin2) (Drop thin1) = Refl
keepHomo (Drop thin2) (Keep thin1) = Refl
keepHomo (Keep thin2) Id = Refl
keepHomo (Keep thin2) (Drop thin) = Refl
keepHomo (Keep thin2) (Keep thin) = Refl

export
keepDrop :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  keep thin2 . Drop thin1 = Drop (thin2 . thin1)
keepDrop Id thin1 = Refl
keepDrop (Drop thin2) thin1 = Refl
keepDrop (Keep thin2) thin1 = Refl
