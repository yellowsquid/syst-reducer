module Total.NormalForm

import Total.Reduction
import Total.Term

public export
data Neutral : Term ctx ty -> Type
public export
data Normal : Term ctx ty -> Type

data Neutral where
  Var : Neutral (Var i)
  App : Neutral t -> Normal u -> Neutral (App t u)
  Rec : Neutral t -> Normal u -> Normal v -> Neutral (Rec t u v)

data Normal where
  Ntrl : Neutral t -> Normal t
  Abs : Normal t -> Normal (Abs t)
  Zero : Normal Zero
  Suc : Normal t -> Normal (Suc t)

%name Neutral n, m, k
%name Normal n, m, k

record NormalForm (0 t : Term ctx ty) where
  constructor MkNf
  term : Term ctx ty
  0 steps : t >= term
  0 normal : Normal term

%name NormalForm nf
