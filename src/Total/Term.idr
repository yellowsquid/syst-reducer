module Total.Term

import public Data.SnocList.Elem
import public Thinning
import Syntax.PreorderReasoning

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

public export
wkn : Term ctx ty -> ctx `Thins` ctx' -> Term ctx' ty
wkn (Var i) thin = Var (index thin i)
wkn (Abs t) thin = Abs (wkn t $ Keep thin)
wkn (App t u) thin = App (wkn t thin) (wkn u thin)
wkn Zero thin = Zero
wkn (Suc t) thin = Suc (wkn t thin)
wkn (Rec t u v) thin = Rec (wkn t thin) (wkn u thin) (wkn v thin)

public export
data Terms : SnocList Ty -> SnocList Ty -> Type where
  Base : ctx `Thins` ctx' -> Terms ctx' ctx
  (:<) : Terms ctx' ctx -> Term ctx' ty -> Terms ctx' (ctx :< ty)

%name Terms sub

public export
index : Terms ctx' ctx -> Elem ty ctx -> Term ctx' ty
index (Base thin) i = Var (index thin i)
index (sub :< t) Here = t
index (sub :< t) (There i) = index sub i

public export
wknAll : Terms ctx' ctx -> ctx' `Thins` ctx'' -> Terms ctx'' ctx
wknAll (Base thin') thin = Base (thin . thin')
wknAll (sub :< t) thin = wknAll sub thin :< wkn t thin

public export
subst : Len ctx' => Term ctx ty -> Terms ctx' ctx -> Term ctx' ty
subst (Var i) sub = index sub i
subst (Abs t) sub = Abs (subst t $ wknAll sub (Drop id) :< Var Here)
subst (App t u) sub = App (subst t sub) (subst u sub)
subst Zero sub = Zero
subst (Suc t) sub = Suc (subst t sub)
subst (Rec t u v) sub = Rec (subst t sub) (subst u sub) (subst v sub)

public export
restrict : Terms ctx'' ctx' -> ctx `Thins` ctx' -> Terms ctx'' ctx
restrict (Base thin') thin = Base (thin' . thin)
restrict (sub :< t) (Drop thin) = restrict sub thin
restrict (sub :< t) (Keep thin) = restrict sub thin :< t

public export
(.) : Len ctx'' => Terms ctx'' ctx' -> Terms ctx' ctx -> Terms ctx'' ctx
sub2 . (Base thin) = restrict sub2 thin
sub2 . (sub1 :< t) = sub2 . sub1 :< subst t sub2

-- Properties ------------------------------------------------------------------

-- Utilities

export
cong3 : (0 f : a -> b -> c -> d) -> x1 = x2 -> y1 = y2 -> z1 = z2 -> f x1 y1 z1 = f x2 y2 z2
cong3 f Refl Refl Refl = Refl

-- Weakening

export
wknHomo :
  (t : Term ctx ty) ->
  (thin1 : ctx `Thins` ctx') ->
  (thin2 : ctx' `Thins` ctx'') ->
  wkn (wkn t thin1) thin2 = wkn t (thin2 . thin1)
wknHomo (Var i) thin1 thin2 =
  cong Var (indexHomo thin2 thin1 i)
wknHomo (Abs t) thin1 thin2 =
  cong Abs (wknHomo t (Keep thin1) (Keep thin2))
wknHomo (App t u) thin1 thin2 =
  cong2 App (wknHomo t thin1 thin2) (wknHomo u thin1 thin2)
wknHomo Zero thin1 thin2 =
  Refl
wknHomo (Suc t) thin1 thin2 =
  cong Suc (wknHomo t thin1 thin2)
wknHomo (Rec t u v) thin1 thin2 =
  cong3 Rec (wknHomo t thin1 thin2) (wknHomo u thin1 thin2) (wknHomo v thin1 thin2)

export
wknId : Len ctx => (t : Term ctx ty) -> wkn t Thinning.id = t
wknId (Var i) = cong Var (indexId i)
wknId (Abs t) = cong Abs (wknId t)
wknId (App t u) = cong2 App (wknId t) (wknId u)
wknId Zero = Refl
wknId (Suc t) = cong Suc (wknId t)
wknId (Rec t u v) = cong3 Rec (wknId t) (wknId u) (wknId v)

indexWknAll :
  (sub : Terms ctx' ctx) ->
  (thin : ctx' `Thins` ctx'') ->
  (i : Elem ty ctx) ->
  index (wknAll sub thin) i = wkn (index sub i) thin
indexWknAll (Base thin') thin i = sym $ cong Var $ indexHomo thin thin' i
indexWknAll (sub :< t) thin Here = Refl
indexWknAll (sub :< t) thin (There i) = indexWknAll sub thin i

wknAllHomo :
  (sub : Terms ctx ctx''') ->
  (thin1 : ctx `Thins` ctx') ->
  (thin2 : ctx' `Thins` ctx'') ->
  wknAll (wknAll sub thin1) thin2 = wknAll sub (thin2 . thin1)
wknAllHomo (Base thin) thin1 thin2 = cong Base (assoc thin2 thin1 thin)
wknAllHomo (sub :< t) thin1 thin2 = cong2 (:<) (wknAllHomo sub thin1 thin2) (wknHomo t thin1 thin2)

-- Restrict

indexRestrict :
  (thin : ctx `Thins` ctx') ->
  (sub : Terms ctx'' ctx') ->
  (i : Elem ty ctx) ->
  index (restrict sub thin) i = index sub (index thin i)
indexRestrict thin (Base thin') i = sym $ cong Var $ indexHomo thin' thin i
indexRestrict (Drop thin) (sub :< t) i = indexRestrict thin sub i
indexRestrict (Keep thin) (sub :< t) Here = Refl
indexRestrict (Keep thin) (sub :< t) (There i) = indexRestrict thin sub i

restrictId : (len : Len ctx) => (sub : Terms ctx' ctx) -> restrict sub (id @{len}) = sub
restrictId (Base thin) = cong Base (identityRight thin)
restrictId {len = S k} (sub :< t) = cong (:< t) (restrictId sub)

restrictHomo :
  (sub : Terms ctx ctx''') ->
  (thin1 : ctx'' `Thins` ctx''') ->
  (thin2 : ctx' `Thins` ctx'') ->
  restrict sub (thin1 . thin2) = restrict (restrict sub thin1) thin2
restrictHomo (Base thin) thin1 thin2 = cong Base (assoc thin thin1 thin2)
restrictHomo (sub :< t) (Drop thin1) thin2 = restrictHomo sub thin1 thin2
restrictHomo (sub :< t) (Keep thin1) (Drop thin2) = restrictHomo sub thin1 thin2
restrictHomo (sub :< t) (Keep thin1) (Keep thin2) = cong (:< t) $ restrictHomo sub thin1 thin2

wknAllRestrict :
  (thin1 : ctx `Thins` ctx') ->
  (sub : Terms ctx'' ctx') ->
  (thin2 : ctx'' `Thins` ctx''') ->
  restrict (wknAll sub thin2) thin1 = wknAll (restrict sub thin1) thin2
wknAllRestrict thin1 (Base thin) thin2 = sym $ cong Base $ assoc thin2 thin thin1
wknAllRestrict (Drop thin) (sub :< t) thin2 = wknAllRestrict thin sub thin2
wknAllRestrict (Keep thin) (sub :< t) thin2 = cong (:< wkn t thin2) (wknAllRestrict thin sub thin2)

-- Substitution & Weakening

export
wknSubst :
  (t : Term ctx ty) ->
  (sub : Terms ctx' ctx) ->
  (thin : ctx' `Thins` ctx'') ->
  wkn (subst t sub) thin = subst t (wknAll sub thin)
wknSubst (Var i) sub thin =
  sym (indexWknAll sub thin i)
wknSubst (Abs t) sub thin =
  cong Abs $ Calc $
    |~ wkn (subst t (wknAll sub (Drop id) :< Var Here)) (Keep thin)
    ~~ subst t (wknAll (wknAll sub (Drop id)) (Keep thin) :< Var (index (Keep thin) Here))
      ...(wknSubst t (wknAll sub (Drop id) :< Var Here) (Keep thin))
    ~~ subst t (wknAll sub (Keep thin . Drop id) :< Var Here)
      ...(cong (subst t . (:< Var Here)) (wknAllHomo sub (Drop id) (Keep thin)))
    ~~ subst t (wknAll sub (Drop id . thin) :< Var Here)
      ...(cong (subst t . (:< Var Here) . wknAll sub . Drop) $ trans (identityRight thin) (sym $ identityLeft thin))
    ~~ subst t (wknAll (wknAll sub thin) (Drop id) :< Var Here)
      ...(sym $ cong (subst t . (:< Var Here)) $ wknAllHomo sub thin (Drop id))
wknSubst (App t u) sub thin =
  cong2 App (wknSubst t sub thin) (wknSubst u sub thin)
wknSubst Zero sub thin =
  Refl
wknSubst (Suc t) sub thin =
  cong Suc (wknSubst t sub thin)
wknSubst (Rec t u v) sub thin =
  cong3 Rec (wknSubst t sub thin) (wknSubst u sub thin) (wknSubst v sub thin)

export
substWkn :
  (t : Term ctx ty) ->
  (thin : ctx `Thins` ctx') ->
  (sub : Terms ctx'' ctx') ->
  subst (wkn t thin) sub = subst t (restrict sub thin)
substWkn (Var i) thin sub =
  sym (indexRestrict thin sub i)
substWkn (Abs t) thin sub =
  cong Abs $ Calc $
    |~ subst (wkn t $ Keep thin) (wknAll sub (Drop id) :< Var Here)
    ~~ subst t (restrict (wknAll sub (Drop id)) thin :< Var Here)
      ...(substWkn t (Keep thin) (wknAll sub (Drop id) :< Var Here))
    ~~ subst t (wknAll (restrict sub thin) (Drop id) :< Var Here)
      ...(cong (subst t . (:< Var Here)) $ wknAllRestrict thin sub (Drop id))
substWkn (App t u) thin sub =
  cong2 App (substWkn t thin sub) (substWkn u thin sub)
substWkn Zero thin sub =
  Refl
substWkn (Suc t) thin sub =
  cong Suc (substWkn t thin sub)
substWkn (Rec t u v) thin sub =
  cong3 Rec (substWkn t thin sub) (substWkn u thin sub) (substWkn v thin sub)

namespace Equiv
  public export
  data Equiv : Terms ctx' ctx -> Terms ctx' ctx -> Type where
    Base : Equiv (Base (Keep thin)) (Base (Drop thin) :< Var Here)
    WknAll :
      (len : Len ctx) =>
      Equiv sub sub' ->
      Equiv
        (wknAll sub (Drop $ id @{len}) :< Var Here)
        (wknAll sub' (Drop $ id @{len}) :< Var Here)

  %name Equiv prf

indexCong : Equiv sub sub' -> (i : Elem ty ctx) -> index sub i = index sub' i
indexCong Base Here = Refl
indexCong Base (There i) = Refl
indexCong (WknAll prf) Here = Refl
indexCong (WknAll {sub, sub'} prf) (There i) = Calc $
  |~ index (wknAll sub (Drop id)) i
  ~~ wkn (index sub i) (Drop id)     ...(indexWknAll sub (Drop id) i)
  ~~ wkn (index sub' i) (Drop id)    ...(cong (flip wkn (Drop id)) $ indexCong prf i)
  ~~ index (wknAll sub' (Drop id)) i ...(sym $ indexWknAll sub' (Drop id) i)

substCong :
  (len : Len ctx') =>
  (t : Term ctx ty) ->
  {0 sub, sub' : Terms ctx' ctx} ->
  Equiv sub sub' ->
  subst t sub = subst t sub'
substCong (Var i) prf = indexCong prf i
substCong (Abs t) prf = cong Abs (substCong t (WknAll prf))
substCong (App t u) prf = cong2 App (substCong t prf) (substCong u prf)
substCong Zero prf = Refl
substCong (Suc t) prf = cong Suc (substCong t prf)
substCong (Rec t u v) prf = cong3 Rec (substCong t prf) (substCong u prf) (substCong v prf)

substBase : (t : Term ctx ty) -> (thin : ctx `Thins` ctx') -> subst t (Base thin) = wkn t thin
substBase (Var i) thin = Refl
substBase (Abs t) thin =
  rewrite identityLeft thin in
  cong Abs $ Calc $
    |~ subst t (Base (Drop thin) :< Var Here)
    ~~ subst t (Base $ Keep thin)             ...(sym $ substCong t Base)
    ~~ wkn t (Keep thin)                      ...(substBase t (Keep thin))
substBase (App t u) thin = cong2 App (substBase t thin) (substBase u thin)
substBase Zero thin = Refl
substBase (Suc t) thin = cong Suc (substBase t thin)
substBase (Rec t u v) thin = cong3 Rec (substBase t thin) (substBase u thin) (substBase v thin)

-- Substitution Composition

indexComp :
  (sub1 : Terms ctx' ctx) ->
  (sub2 : Terms ctx'' ctx') ->
  (i : Elem ty ctx) ->
  index (sub2 . sub1) i = subst (index sub1 i) sub2
indexComp (Base thin) sub2 i = indexRestrict thin sub2 i
indexComp (sub1 :< t) sub2 Here = Refl
indexComp (sub1 :< t) sub2 (There i) = indexComp sub1 sub2 i

wknAllComp :
  (sub1 : Terms ctx' ctx) ->
  (sub2 : Terms ctx'' ctx') ->
  (thin : ctx'' `Thins` ctx''') ->
  wknAll sub2 thin . sub1 = wknAll (sub2 . sub1) thin
wknAllComp (Base thin') sub2 thin = wknAllRestrict thin' sub2 thin
wknAllComp (sub1 :< t) sub2 thin =
  cong2 (:<)
    (wknAllComp sub1 sub2 thin)
    (sym $ wknSubst t sub2 thin)

compDrop :
  (sub1 : Terms ctx' ctx) ->
  (thin : ctx' `Thins` ctx'') ->
  (sub2 : Terms ctx''' ctx'') ->
  sub2 . wknAll sub1 thin = restrict sub2 thin . sub1
compDrop (Base thin') thin sub2 = restrictHomo sub2 thin thin'
compDrop (sub1 :< t) thin sub2 = cong2 (:<) (compDrop sub1 thin sub2) (substWkn t thin sub2)

export
compWknAll :
  (sub1 : Terms ctx' ctx) ->
  (sub2 : Terms ctx''' ctx'') ->
  (thin : ctx' `Thins` ctx'') ->
  sub2 . wknAll sub1 thin = restrict sub2 thin . sub1
compWknAll (Base thin') sub2 thin = restrictHomo sub2 thin thin'
compWknAll (sub1 :< t) sub2 thin = cong2 (:<) (compWknAll sub1 sub2 thin) (substWkn t thin sub2)

export
baseComp :
  (thin : ctx' `Thins` ctx'') ->
  (sub : Terms ctx' ctx) ->
  Base thin . sub = wknAll sub thin
baseComp thin (Base thin') = Refl
baseComp thin (sub :< t) = cong2 (:<) (baseComp thin sub) (substBase t thin)

-- Substitution

export
substId : (len : Len ctx) => (t : Term ctx ty) -> subst t (Base $ id @{len}) = t
substId (Var i) = cong Var (indexId i)
substId (Abs t) =
  rewrite identitySquared len in
  cong Abs $ trans (sym $ substCong t Base) (substId t)
substId (App t u) = cong2 App (substId t) (substId u)
substId Zero = Refl
substId (Suc t) = cong Suc (substId t)
substId (Rec t u v) = cong3 Rec (substId t) (substId u) (substId v)

export
substHomo :
  (t : Term ctx ty) ->
  (sub1 : Terms ctx' ctx) ->
  (sub2 : Terms ctx'' ctx') ->
  subst (subst t sub1) sub2 = subst t (sub2 . sub1)
substHomo (Var i) sub1 sub2 =
  sym $ indexComp sub1 sub2 i
substHomo (Abs t) sub1 sub2 =
  cong Abs $ Calc $
    |~ subst (subst t (wknAll sub1 (Drop id) :< Var Here)) (wknAll sub2 (Drop id) :< Var Here)
    ~~ subst t ((wknAll sub2 (Drop id) :< Var Here) . (wknAll sub1 (Drop id) :< Var Here))
      ...(substHomo t (wknAll sub1 (Drop id) :< Var Here) (wknAll sub2 (Drop id) :< Var Here))
    ~~ subst t ((wknAll sub2 (Drop id) :< Var Here) . wknAll sub1 (Drop id) :< Var Here)
      ...(Refl)
    ~~ subst t (restrict (wknAll sub2 (Drop id)) id . sub1 :< Var Here)
      ...(cong (subst t . (:< Var Here)) $ compDrop sub1 (Drop id) (wknAll sub2 (Drop id) :< Var Here))
    ~~ subst t (wknAll sub2 (Drop id) . sub1 :< Var Here)
      ...(cong (subst t . (:< Var Here) . (. sub1)) $ restrictId (wknAll sub2 (Drop id)))
    ~~ subst t (wknAll (sub2 . sub1) (Drop id) :< Var Here)
      ...(cong (subst t . (:< Var Here)) $ wknAllComp sub1 sub2 (Drop id))
substHomo (App t u) sub1 sub2 =
  cong2 App (substHomo t sub1 sub2) (substHomo u sub1 sub2)
substHomo Zero sub1 sub2 =
  Refl
substHomo (Suc t) sub1 sub2 =
  cong Suc (substHomo t sub1 sub2)
substHomo (Rec t u v) sub1 sub2 =
  cong3 Rec (substHomo t sub1 sub2) (substHomo u sub1 sub2) (substHomo v sub1 sub2)
