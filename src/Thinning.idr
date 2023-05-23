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

export
keep : sx `Thins` sy -> sx :< z `Thins` sy :< z
keep Id = Id
keep (Drop thin) = Keep (Drop thin)
keep (Keep thin) = Keep (Keep thin)

-- Operations ------------------------------------------------------------------

export
index : sx `Thins` sy -> Elem z sx -> Elem z sy
index Id i = i
index (Drop thin) i = There (index thin i)
index (Keep thin) Here = Here
index (Keep thin) (There i) = There (index thin i)

export
(.) : sy `Thins` sz -> sx `Thins` sy -> sx `Thins` sz
compNotId :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  {auto 0 _ : NotId thin2} ->
  {auto 0 _ : NotId thin1} ->
  NotId (thin2 . thin1)

Id . thin1 = thin1
(Drop thin2) . thin1 = Drop (thin2 . thin1)
(Keep thin2) . Id = Keep thin2
(Keep thin2) . (Drop thin1) = Drop (thin2 . thin1)
(Keep thin2) . (Keep thin1) = Keep {prf = compNotId thin2 thin1} (thin2 . thin1)

compNotId (Drop thin2) thin1 = DropNotId
compNotId (Keep thin2) (Drop thin1) = DropNotId
compNotId (Keep thin2) (Keep thin1) = KeepNotId (compNotId thin2 thin1)
