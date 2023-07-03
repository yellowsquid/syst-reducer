module Term.Semantics

import Control.Monad.Identity
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
fullSem' (Lit n) = pure (const n)
fullSem' (Suc t) = do
  t <- fullSem' t
  pure (S . t)
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
