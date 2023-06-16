||| A setoid of context thinnings.
module Thinning

import Control.Order
import Control.Relation
import Data.Either
import Data.Nat
import Syntax.PreorderReasoning

import public Data.SnocList.Elem

%prefix_record_projections off

infix 4 <~>

-- Definition ------------------------------------------------------------------

||| An injective, order-preserving map from one context to another.
public export
data Thins : SnocList a -> SnocList a -> Type where
  ||| Identity map.
  Id : sx `Thins` sx
  ||| Empty map.
  Empty : [<] `Thins` sx
  ||| Skips over an element in the target context.
  Drop : sx `Thins` sy -> sx `Thins` sy :< y
  ||| Extends both contexts with a new element.
  Keep : sx `Thins` sy -> sx :< z `Thins` sy :< z

%name Thins thin

||| Apply a thinning to an element of the source context.
export
index : sx `Thins` sy -> Elem x sx -> Elem x sy
index Id i = i
index (Drop thin) i = There (index thin i)
index (Keep thin) Here = Here
index (Keep thin) (There i) = There (index thin i)

||| An equivalence relation on thinnings. Two thinnings are equal if they have
||| the same action on elements.
public export
record (<~>) (thin1, thin2 : sx `Thins` sy) where
  constructor MkEquivalence
  equiv : forall x. (i : Elem x sx) -> index thin1 i = index thin2 i

%name (<~>) prf

--- Properties

-- Relational

export
irrelevantEquiv :
  {0 thin1, thin2 : sx `Thins` sy} ->
  (0 prf : thin1 <~> thin2) ->
  thin1 <~> thin2
irrelevantEquiv prf = MkEquivalence (\i => irrelevantEq $ prf.equiv i)

export
Reflexive (sx `Thins` sy) (<~>) where
  reflexive = MkEquivalence (\i => Refl)

export
Symmetric (sx `Thins` sy) (<~>) where
  symmetric prf = MkEquivalence (\i => sym $ prf.equiv i)

export
Transitive (sx `Thins` sy) (<~>) where
  transitive prf1 prf2 = MkEquivalence (\i => trans (prf1.equiv i) (prf2.equiv i))

export
Equivalence (sx `Thins` sy) (<~>) where

export
Preorder (sx `Thins` sy) (<~>) where

export
dropCong : thin1 <~> thin2 -> Drop thin1 <~> Drop thin2
dropCong prf = MkEquivalence (\i => cong There $ prf.equiv i)

export
keepCong : thin1 <~> thin2 -> Keep thin1 <~> Keep thin2
keepCong prf = MkEquivalence
  (\i =>
    case i of
      Here => Refl
      There i => cong There $ prf.equiv i)

-- Indexing

export
indexId : (i : Elem x sx) -> index Id i = i
indexId i = Refl

export
indexDrop :
  (thin : sx `Thins` sy) ->
  (i : Elem x sx) ->
  index (Drop thin) i = There (index thin i)
indexDrop thin i = Refl

export
indexKeepHere : (thin : sx `Thins` sy) -> index (Keep thin) Here = Here
indexKeepHere thin = Refl

export
indexKeepThere :
  (thin : sx `Thins` sy) ->
  (i : Elem x sx) ->
  index (Keep thin) (There i) = There (index thin i)
indexKeepThere thin i = Refl

-- Other

thinToEmpty : sx `Thins` [<] -> sx = [<]
thinToEmpty Id = Refl
thinToEmpty Empty = Refl

0 thinLen : sx `Thins` sy -> length sx `LTE` length sy
thinLen Id = reflexive
thinLen Empty = LTEZero
thinLen (Drop thin) = lteSuccRight (thinLen thin)
thinLen (Keep thin) = LTESucc (thinLen thin)

idUnique' : (thin : sx `Thins` sx) -> (i : Elem x sx) -> index thin i = i
idUnique' Id i = Refl
idUnique' (Drop thin) i = void $ LTEImpliesNotGT (thinLen thin) reflexive
idUnique' (Keep thin) Here = Refl
idUnique' (Keep thin) (There i) = cong There $ idUnique' thin i

export
idUnique : (thin1, thin2 : sx `Thins` sx) -> thin1 <~> thin2
idUnique thin1 thin2 =
  MkEquivalence
    (\i => trans (idUnique' thin1 i) (sym $ idUnique' thin2 i))

export
emptyUnique : (thin1, thin2 : [<] `Thins` sx) -> thin1 <~> thin2
emptyUnique thin1 thin2 = MkEquivalence (\i => absurd i)

-- Smart Constructors ----------------------------------------------------------

||| Point map. The representable thinning of an element.
export
Point : Elem x sx -> [<x] `Thins` sx
Point Here = Keep Empty
Point (There i) = Drop (Point i)

export
indexPoint : (i : Elem x sx) -> index (Point i) Here = i
indexPoint Here = Refl
indexPoint (There i) = cong There $ indexPoint i

export
pointCong : {0 i, j : Elem x sx} -> i = j -> Point i <~> Point j
pointCong prf = MkEquivalence (\Here => cong (\i => index (Point i) Here) prf)

export
dropPoint : (i : Elem x sx) -> Drop (Point i) <~> Point (There i)
dropPoint i = MkEquivalence (\Here => Refl)

export
keepEmptyIsPoint : Keep Empty <~> Point Here
keepEmptyIsPoint = MkEquivalence (\Here => Refl)

-- Operations ------------------------------------------------------------------

||| Composition of two thinnings.
export
(.) : sy `Thins` sz -> sx `Thins` sy -> sx `Thins` sz
Id . thin1 = thin1
Empty . Id = Empty
Empty . Empty = Empty
Drop thin2 . Id = Drop thin2
Drop thin2 . Empty = Empty
Drop thin2 . Drop thin1 = Drop (thin2 . Drop thin1)
Drop thin2 . Keep thin1 = Drop (thin2 . Keep thin1)
Keep thin2 . Id = Keep thin2
Keep thin2 . Empty = Empty
Keep thin2 . Drop thin1 = Drop (thin2 . thin1)
Keep thin2 . Keep thin1 = Keep (thin2 . thin1)

--- Properties

export
indexHomo :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  (i : Elem x sx) ->
  index thin2 (index thin1 i) = index (thin2 . thin1) i
indexHomo Id thin1 i = Refl
indexHomo Empty Id i impossible
indexHomo Empty Empty i impossible
indexHomo (Drop thin2) Id i = Refl
indexHomo (Drop thin2) (Drop thin1) i = cong There $ indexHomo thin2 (Drop thin1) i
indexHomo (Drop thin2) (Keep thin1) i = cong There $ indexHomo thin2 (Keep thin1) i
indexHomo (Keep thin2) Id i = Refl
indexHomo (Keep thin2) (Drop thin1) i = cong There $ indexHomo thin2 thin1 i
indexHomo (Keep thin2) (Keep thin1) Here = Refl
indexHomo (Keep thin2) (Keep thin1) (There i) = cong There $ indexHomo thin2 thin1 i

-- Categorical

export
identityLeft : (thin : sx `Thins` sy) -> Id . thin <~> thin
identityLeft thin = reflexive

export
identityRight : (thin : sx `Thins` sy) -> thin . Id <~> thin
identityRight Id = reflexive
identityRight Empty = reflexive
identityRight (Drop thin) = reflexive
identityRight (Keep thin) = reflexive

export
assoc :
  (thin3 : sz `Thins` sw) ->
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  thin3 . (thin2 . thin1) <~> (thin3 . thin2) . thin1
assoc thin3 thin2 thin1 = MkEquivalence (\i => Calc $
  |~ index (thin3 . (thin2 . thin1)) i
  ~~ index thin3 (index (thin2 . thin1) i)     ..<(indexHomo thin3 (thin2 . thin1) i)
  ~~ index thin3 (index thin2 (index thin1 i)) ..<(cong (index thin3) $ indexHomo thin2 thin1 i)
  ~~ index (thin3 . thin2) (index thin1 i)     ...(indexHomo thin3 thin2 (index thin1 i))
  ~~ index ((thin3 . thin2) . thin1) i         ...(indexHomo (thin3 . thin2) thin1) i)

-- Other

export
dropLeft :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  Drop thin2 . thin1 <~> Drop (thin2 . thin1)
dropLeft thin2 Id = symmetric $ dropCong $ identityRight thin2
dropLeft thin2 Empty = emptyUnique Empty (Drop (thin2 . Empty))
dropLeft thin2 (Drop thin1) = reflexive
dropLeft thin2 (Keep thin1) = reflexive

export
keepDrop :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  Keep thin2 . Drop thin1 <~> Drop (thin2 . thin1)
keepDrop thin2 thin1 = reflexive

export
keepHomo :
  (thin2 : sy `Thins` sz) ->
  (thin1 : sx `Thins` sy) ->
  Keep thin2 . Keep thin1 <~> Keep (thin2 . thin1)
keepHomo thin2 thin1 = reflexive

export
pointRight :
  (thin : sx `Thins` sy) ->
  (i : Elem x sx) ->
  thin . Point i <~> Point (index thin i)
pointRight Id i = reflexive
pointRight (Drop thin) i = transitive (dropLeft thin (Point i)) (dropCong (pointRight thin i))
pointRight (Keep thin) Here = keepCong (emptyUnique (thin . Empty) Empty)
pointRight (Keep thin) (There i) = dropCong (pointRight thin i)

-- Coverings and Coproducts ----------------------------------------------------

||| Proof that the thinnings are jointly surjective.
public export
record Covering (thin1 : sx `Thins` sz) (thin2 : sy `Thins` sz) where
  constructor MkCovering
  covers :
    forall x.
    (i : Elem x sz) ->
    Either (j ** index thin1 j = i) (k ** index thin2 k = i)

||| Unique thinning that factors into a covering.
public export
record Coproduct (thin1 : sx `Thins` sz) (thin2 : sy `Thins` sz) where
  constructor MkCoproduct
  {0 sw : SnocList _}
  {thin1' : sx `Thins` sw}
  {thin2' : sy `Thins` sw}
  {factor : sw `Thins` sz}
  0 left : factor . thin1' <~> thin1
  0 right : factor . thin2' <~> thin2
  0 cover : Covering thin1' thin2'

%name Covering cover
%name Coproduct cp

--- Properties

-- Coverings

coverSym : Covering thin1 thin2 -> Covering thin2 thin1
coverSym cover = MkCovering (\i => mirror $ cover.covers i)

coverId : (0 thin : sx `Thins` sy) -> Covering Id thin
coverId thin = MkCovering (\i => Left (i ** Refl))

coverDropKeep : Covering thin1 thin2 -> Covering (Drop thin1) (Keep thin2)
coverDropKeep cover = MkCovering
  (\i => case i of
    Here => Right (Here ** Refl)
    There i => case cover.covers i of
      Left (j ** prf) => Left (j ** cong There prf)
      Right (k ** prf) => Right (There k ** cong There prf))

coverKeepDrop : Covering thin1 thin2 -> Covering (Keep thin1) (Drop thin2)
coverKeepDrop cp = coverSym $ coverDropKeep $ coverSym cp

coverKeepKeep : Covering thin1 thin2 -> Covering (Keep thin1) (Keep thin2)
coverKeepKeep cover = MkCovering
  (\i => case i of
    Here => Left (Here ** Refl)
    There i => case cover.covers i of
      Left (j ** prf) => Left (There j ** cong There prf)
      Right (k ** prf) => Right (There k ** cong There prf))

-- Coproducts

coprodSym : Coproduct thin1 thin2 -> Coproduct thin2 thin1
coprodSym cp = MkCoproduct cp.right cp.left (coverSym cp.cover)

coprodId : (thin : sx `Thins` sy) -> Coproduct Id thin
coprodId thin =
  MkCoproduct
    { thin1' = Id
    , thin2' = thin
    , factor = Id
    , left = reflexive
    , right = reflexive
    , cover = coverId thin
    }

coprodEmpty : (thin : sx `Thins` sy) -> Coproduct Empty thin
coprodEmpty thin =
  MkCoproduct
    { thin1' = Empty
    , thin2' = Id
    , factor = thin
    , left = emptyUnique (thin . Empty) Empty
    , right = identityRight thin
    , cover = coverSym $ coverId Empty
    }

||| Finds the coproduct of two thinnings.
export
coprod :
  (thin1 : sx `Thins` sz) ->
  (thin2 : sy `Thins` sz) ->
  Coproduct thin1 thin2
coprod Id thin2 = coprodId thin2
coprod Empty thin2 = coprodEmpty thin2
coprod (Drop thin1) Id = coprodSym $ coprodId (Drop thin1)
coprod (Drop thin1) Empty = coprodSym $ coprodEmpty (Drop thin1)
coprod (Drop thin1) (Drop thin2) =
  let cp = coprod thin1 thin2 in
  MkCoproduct
    { thin1' = cp.thin1'
    , thin2' = cp.thin2'
    , factor = Drop cp.factor
    , left = transitive (dropLeft cp.factor cp.thin1') (dropCong cp.left)
    , right = transitive (dropLeft cp.factor cp.thin2') (dropCong cp.right)
    , cover = cp.cover
    }
coprod (Drop thin1) (Keep thin2) =
  let cp = coprod thin1 thin2 in
  MkCoproduct
    { thin1' = Drop cp.thin1'
    , thin2' = Keep cp.thin2'
    , factor = Keep cp.factor
    , left = transitive (keepDrop cp.factor cp.thin1') (dropCong cp.left)
    , right = transitive (keepHomo cp.factor cp.thin2') (keepCong cp.right)
    , cover = coverDropKeep cp.cover
    }
coprod (Keep thin1) Id = coprodSym $ coprodId (Keep thin1)
coprod (Keep thin1) Empty = coprodSym $ coprodEmpty (Keep thin1)
coprod (Keep thin1) (Drop thin2) =
  let cp = coprod thin1 thin2 in
  MkCoproduct
    { thin1' = Keep cp.thin1'
    , thin2' = Drop cp.thin2'
    , factor = Keep cp.factor
    , left = transitive (keepHomo cp.factor cp.thin1') (keepCong cp.left)
    , right = transitive (keepDrop cp.factor cp.thin2') (dropCong cp.right)
    , cover = coverKeepDrop cp.cover
    }
coprod (Keep thin1) (Keep thin2) =
  let cp = coprod thin1 thin2 in
  MkCoproduct
    { thin1' = Keep cp.thin1'
    , thin2' = Keep cp.thin2'
    , factor = Keep cp.factor
    , left = transitive (keepHomo cp.factor cp.thin1') (keepCong cp.left)
    , right = transitive (keepHomo cp.factor cp.thin2') (keepCong cp.right)
    , cover = coverKeepKeep cp.cover
    }

-- Coproduct Equivalence -------------------------------------------------------

namespace Coproduct
  public export
  data (<~>) :
    {0 thin1 : sx `Thins` sa} ->
    {0 thin2 : sy `Thins` sa} ->
    {0 thin3 : sz `Thins` sa} ->
    {0 thin4 : sw `Thins` sa} ->
    Coproduct thin1 thin2 ->
    Coproduct thin3 thin4 ->
    Type
    where
