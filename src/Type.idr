module Type

infixr 9 ~>

public export
data Ty : Type where
  N : Ty
  (~>) : Ty -> Ty -> Ty

%name Ty ty

public export
(<+>) : Ty -> Ty -> Ty
N <+> N = N
N <+> (ty2 ~> ty2') = ty2 ~> (N <+> ty2')
(ty1 ~> ty1') <+> N = ty1 ~> (ty1' <+> N)
(ty1 ~> ty1') <+> (ty2 ~> ty2') = (ty1 <+> ty2) ~> (ty1' <+> ty2')
