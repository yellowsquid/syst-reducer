module Type

infixr 9 ~>

public export
data Ty : Type where
  N : Ty
  (~>) : Ty -> Ty -> Ty

%name Ty ty
