module Term

import Data.SnocList.Elem
import Thinning

infixr 20 ~>

-- Types -----------------------------------------------------------------------

public export
data Ty : Type where
  N : Ty
  (~>) : Ty -> Ty -> Ty

%name Ty ty

-- Terms -----------------------------------------------------------------------

public export
data Term : SnocList Ty -> Ty -> Type
public export
data Subst : SnocList Ty -> SnocList Ty -> Type

data Term where
  Var : (i : Elem ty ctx) -> Term ctx ty
  Abs : Term (ctx :< ty) ty' -> Term ctx (ty ~> ty')
  App : Term ctx (ty ~> ty') -> Term ctx ty -> Term ctx ty'
  Zero : Term ctx N
  Succ : Term ctx N -> Term ctx N
  Rec : Term ctx N -> Term ctx ty -> Term (ctx :< ty) ty -> Term ctx ty
  Sub : Term ctx ty -> Subst ctx' ctx -> Term ctx' ty

data Subst where
  Base : ctx' `Thins` ctx -> Subst ctx ctx'
  (:<) : Subst ctx ctx' -> Term ctx ty -> Subst ctx (ctx' :< ty)

%name Term t, u, v
%name Subst sub

shift : Subst ctx ctx' -> Subst (ctx :< ty) ctx'
shift (Base thin) = Base (Drop thin)
shift (sub :< t) = shift sub :< Sub t (Base (Drop Id))

export
lift : Subst ctx ctx' -> Subst (ctx :< ty) (ctx' :< ty)
lift (Base thin) = Base (keep thin)
lift (sub :< t) = shift (sub :< t) :< Var Here

public export
index : Subst ctx' ctx -> Elem ty ctx -> Term ctx' ty
index (Base thin) i = Var (index thin i)
index (sub :< t) Here = t
index (sub :< t) (There i) = index sub i

public export
restrict : Subst ctx1 ctx2 -> ctx3 `Thins` ctx2 -> Subst ctx1 ctx3
restrict (Base thin') thin = Base (thin' . thin)
restrict (sub :< t) Id = sub :< t
restrict (sub :< t) (Drop thin) = restrict sub thin
restrict (sub :< t) (Keep thin) = restrict sub thin :< t

export
(.) : Subst ctx1 ctx2 -> Subst ctx2 ctx3 -> Subst ctx1 ctx3
sub2 . Base thin = restrict sub2 thin
sub2 . (sub1 :< t) = sub2 . sub1 :< Sub t sub2

-- Equivalence -----------------------------------------------------------------

public export
data Equiv : Term ctx ty -> Term ctx ty -> Type where
  Refl : Equiv t t
  Sym : Equiv t u -> Equiv u t
  Trans : Equiv t u -> Equiv u v -> Equiv t v
  AbsCong : Equiv t u -> Equiv (Abs t) (Abs u)
  AppCong : Equiv t1 t2 -> Equiv u1 u2 -> Equiv (App t1 u1) (App t2 u2)
  SuccCong : Equiv t u -> Equiv (Succ t) (Succ u)
  RecCong : Equiv t1 t2 -> Equiv u1 u2 -> Equiv v1 v2 -> Equiv (Rec t1 u1 v1) (Rec t2 u2 v2)
  PiBeta : Equiv (App (Abs t) u) (Sub t (Base Id :< u))
  NatBetaZ : Equiv (Rec Zero t u) t
  NatBetaS : Equiv (Rec (Succ t) u v) (Sub v (Base Id :< Rec t u v))
  SubVar : Equiv (Sub (Var i) sub) (index sub i)
  SubAbs : Equiv (Sub (Abs t) sub) (Abs (Sub t $ lift sub))
  SubApp : Equiv (Sub (App t u) sub) (App (Sub t sub) (Sub u sub))
  SubZero : Equiv (Sub Zero sub) Zero
  SubSucc : Equiv (Sub (Succ t) sub) (Succ (Sub t sub))
  SubRec : Equiv (Sub (Rec t u v) sub) (Rec (Sub t sub) (Sub u sub) (Sub v $ lift sub))
  SubSub : Equiv (Sub (Sub t sub1) sub2) (Sub t (sub2 . sub1))
