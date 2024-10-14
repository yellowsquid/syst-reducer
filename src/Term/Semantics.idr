module Term.Semantics

import Control.Monad.Identity
import Data.Nat
import Term

import public Data.SnocList.Quantifiers

public export
TypeOf : Ty -> Type
TypeOf N = Nat
TypeOf (ty ~> ty') = TypeOf ty -> TypeOf ty'

rec : Nat -> a -> (a -> a) -> a
rec 0 x f = x
rec (S k) x f = f (rec k x f)

%inline
init : All p (sx :< x) -> All p sx
init (psx :< px) = psx

%inline
mapInit : (All p sx -> All p sy) -> All p (sx :< z) -> All p (sy :< z)
mapInit f (psx :< px) = f psx :< px

restrict : Applicative m => sx `Thins` sy -> m (All p sy -> All p sx)
restrict Id = pure id
restrict Empty = pure (const [<])
restrict (Drop thin) = [| restrict thin . [| init |] |]
restrict (Keep thin) = [| mapInit (restrict thin) |]

%inline
indexVar : All p [<x] -> p x
indexVar [<px] = px

arb : (ty : Ty) -> TypeOf ty
arb N = 0
arb (ty ~> ty') = const (arb ty')

-- swap : (ty1, ty2 : Ty) -> TypeOf (ty1 <+> ty2) -> TypeOf (ty2 <+> ty1)
-- swap N N = id
-- swap N (ty2 ~> ty2') = (swap N ty2' .)
-- swap (ty1 ~> ty1') N = (swap ty1' N .)
-- swap (ty1 ~> ty1') (ty2 ~> ty2') = (swap ty1' ty2' .) . (. swap ty2 ty1)

-- inl : (ty1, ty2 : Ty) -> TypeOf ty1 -> TypeOf (ty1 <+> ty2)
-- prl : (ty1, ty2 : Ty) -> TypeOf (ty1 <+> ty2) -> TypeOf ty1

-- inl N N = id
-- inl N (ty2 ~> ty2') = const . inl N ty2'
-- inl (ty1 ~> ty1') N = (inl ty1' N .)
-- inl (ty1 ~> ty1') (ty2 ~> ty2') = (inl ty1' ty2' .) . (. prl ty1 ty2)

-- prl N N = id
-- prl N (ty2 ~> ty2') = prl N ty2' . ($ arb ty2)
-- prl (ty1 ~> ty1') N = (prl ty1' N .)
-- prl (ty1 ~> ty1') (ty2 ~> ty2') = (prl ty1' ty2' .) . (. inl ty1 ty2)

%inline
opSem : Operator tys ty -> TypeOf (foldr (~>) ty tys)
opSem (Lit n) = n
opSem Suc = S
opSem Plus = (+)
opSem Mult = (*)
opSem Pred = pred
opSem Minus = minus
opSem Div = div
opSem Mod = mod
-- opSem (Inl ty1 ty2) = inl ty1 ty2
-- opSem (Inr ty1 ty2) = swap ty2 ty1 . inl ty2 ty1
-- opSem (Prl ty1 ty2) = prl ty1 ty2
-- opSem (Prr ty1 ty2) = prl ty2 ty1 . swap ty1 ty2

%inline
sem' : Monad m => Term ty ctx -> m (All TypeOf ctx -> TypeOf ty)
fullSem' : Monad m => FullTerm ty ctx -> m (All TypeOf ctx -> TypeOf ty)

sem' (t `Over` thin) = [| fullSem' t . restrict thin |]

fullSem' Var = pure indexVar
fullSem' (Const t) = do
  t <- fullSem' t
  pure (const . t)
fullSem' (Abs t) = do
  t <- fullSem' t
  pure (t .: (:<))
fullSem' (App (MakePair t u _)) = do
  t <- sem' t
  u <- sem' u
  pure (\ctx => t ctx (u ctx))
fullSem' (Op op) = pure (const $ opSem op)
fullSem' (Rec (MakePair t (MakePair u v _ `Over` thin) _)) = do
  t <- sem' t
  u <- sem' u
  v <- sem' v
  f <- restrict thin
  pure
    (\ctx =>
      let ctx' = f ctx in
      rec (t ctx) (u ctx') (v ctx'))

export
sem : Term ty ctx -> All TypeOf ctx -> TypeOf ty
sem t = runIdentity (sem' t)
