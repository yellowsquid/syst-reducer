module Total.Term

import public Data.SnocList.Elem
import public Thinning

%prefix_record_projections off

infixr 10 ~>

public export
data Ty : Type where
  N : Ty
  (~>) : Ty -> Ty -> Ty

%name Ty ty

public export
data Term : SnocList Ty -> Ty -> Type where
  Var : (i : Elem ty ctx) -> Term ctx ty
  Abs : Term (ctx :< ty) ty' -> Term ctx (ty ~> ty')
  App : {ty : Ty} -> Term ctx (ty ~> ty') -> Term ctx ty -> Term ctx ty'
  Zero : Term ctx N
  Suc : Term ctx N -> Term ctx N
  Rec : Term ctx N -> Term ctx ty -> Term ctx (ty ~> ty) -> Term ctx ty

%name Term t, u, v

wkn : Term ctx ty -> ctx `Thins` ctx' -> Term ctx' ty
wkn (Var i) thin = Var (index thin i)
wkn (Abs t) thin = Abs (wkn t $ keep thin)
wkn (App t u) thin = App (wkn t thin) (wkn u thin)
wkn Zero thin = Zero
wkn (Suc t) thin = Suc (wkn t thin)
wkn (Rec t u v) thin = Rec (wkn t thin) (wkn u thin) (wkn v thin)

public export
data Terms : SnocList Ty -> SnocList Ty -> Type where
  Base : ctx `Thins` ctx' -> Terms ctx' ctx
  (:<) : Terms ctx' ctx -> Term ctx' ty -> Terms ctx' (ctx :< ty)

%name Terms sub

index : Terms ctx' ctx -> Elem ty ctx -> Term ctx' ty
index (Base thin) i = Var (index thin i)
index (sub :< t) Here = t
index (sub :< t) (There i) = index sub i

wknAll : Terms ctx' ctx -> ctx' `Thins` ctx'' -> Terms ctx'' ctx
wknAll (Base thin') thin = Base (thin . thin')
wknAll (sub :< t) thin = wknAll sub thin :< wkn t thin

export
subst : Term ctx ty -> Terms ctx' ctx -> Term ctx' ty
subst (Var i) sub = index sub i
subst (Abs t) sub = Abs (subst t $ wknAll sub (Drop Id) :< Var Here)
subst (App t u) sub = App (subst t sub) (subst u sub)
subst Zero sub = Zero
subst (Suc t) sub = Suc (subst t sub)
subst (Rec t u v) sub = Rec (subst t sub) (subst u sub) (subst v sub)

restrict : Terms ctx'' ctx' -> ctx `Thins` ctx' -> Terms ctx'' ctx
restrict (Base thin') thin = Base (thin' . thin)
restrict (sub :< t) Id = sub :< t
restrict (sub :< t) (Drop thin) = restrict sub thin
restrict (sub :< t) (Keep thin) = restrict sub thin :< t

(.) : Terms ctx'' ctx' -> Terms ctx' ctx -> Terms ctx'' ctx
sub2 . (Base thin) = restrict sub2 thin
sub2 . (sub1 :< t) = sub2 . sub1 :< subst t sub2
