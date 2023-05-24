module NormalForm

import Data.SnocList.Elem
import Term
import Thinning

-- Neutrals and Normals --------------------------------------------------------

public export
data IsNeutral : Term ctx ty -> Type
public export
data IsNormal : Term ctx ty -> Type

data IsNeutral where
  Var : IsNeutral (Var i)
  App : IsNeutral t -> IsNormal u -> IsNeutral (App t u)
  Rec : IsNeutral t -> IsNormal u -> IsNormal v -> IsNeutral (Rec t u v)

data IsNormal where
  Ntrl : IsNeutral t -> IsNormal t
  Abs : IsNormal t -> IsNormal (Abs t)
  Zero : IsNormal Zero
  Succ : IsNormal t -> IsNormal (Succ t)

%name IsNeutral prf
%name IsNormal prf

public export
record Normal (ctx : SnocList Ty) (ty : Ty) where
  constructor MkNormal
  forget : Term ctx ty
  0 isNormal : IsNormal forget

%name Normal n, m, k

-- Inversions ------------------------------------------------------------------

export
predNorm : IsNormal (Succ t) -> IsNormal t
predNorm (Succ prf) = prf

export
appNtrl : IsNormal (App t u) -> IsNeutral (App t u)
appNtrl (Ntrl prf) = prf

export
recNtrl : IsNormal (Rec t u v) -> IsNeutral (Rec t u v)
recNtrl (Ntrl prf) = prf
