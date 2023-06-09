module Total.Term.CoDebruijn

import public Data.SnocList.Elem
import public Thinning
import Syntax.PreorderReasoning
import Total.Term

%prefix_record_projections off

-- Definition ------------------------------------------------------------------

public export
data CoTerm : Ty -> SnocList Ty -> Type where
  Var : CoTerm ty [<ty]
  Abs : Binds [<ty] (CoTerm ty') ctx -> CoTerm (ty ~> ty') ctx
  App : {ty : Ty} -> Pair (CoTerm (ty ~> ty')) (CoTerm ty) ctx -> CoTerm ty' ctx
  Zero : CoTerm N [<]
  Suc : CoTerm N ctx -> CoTerm N ctx
  Rec : Pair (CoTerm N) (Pair (CoTerm ty) (CoTerm (ty ~> ty))) ctx -> CoTerm ty ctx

%name CoTerm t, u, v

public export
FullTerm : Ty -> SnocList Ty -> Type
FullTerm ty ctx = Thinned (CoTerm ty) ctx

-- Smart Constructors ----------------------------------------------------------

public export
var : Len ctx => Elem ty ctx -> FullTerm ty ctx
var i = Var `Over` point i

public export
abs : FullTerm ty' (ctx :< ty) -> FullTerm (ty ~> ty') ctx
abs = map Abs . MkBound (S Z)

public export
app : {ty : Ty} -> FullTerm (ty ~> ty') ctx -> FullTerm ty ctx -> FullTerm ty' ctx
app t u = map App (MkPair t u)

public export
zero : Len ctx => FullTerm N ctx
zero = Zero `Over` empty

public export
suc : FullTerm N ctx -> FullTerm N ctx
suc = map Suc

public export
rec : FullTerm N ctx -> FullTerm ty ctx -> FullTerm (ty ~> ty) ctx -> FullTerm ty ctx
rec t u v = map Rec $ MkPair t (MkPair u v)

-- Substitutions ---------------------------------------------------------------

public export
data CoTerms : SnocList Ty -> SnocList Ty -> Type where
  Lin : CoTerms [<] ctx'
  (:<) : CoTerms ctx ctx' -> FullTerm ty ctx' -> CoTerms (ctx :< ty) ctx'

%name CoTerms sub

public export
index : CoTerms ctx ctx' -> Elem ty ctx -> FullTerm ty ctx'
index (sub :< t) Here = t
index (sub :< t) (There i) = index sub i

public export
wknAll : CoTerms ctx ctx' -> ctx' `Thins` ctx'' -> CoTerms ctx ctx''
wknAll [<] thin = [<]
wknAll (sub :< t) thin = wknAll sub thin :< wkn t thin

public export
shift : CoTerms ctx ctx' -> CoTerms ctx (ctx' :< ty)
shift [<] = [<]
shift (sub :< t) = shift sub :< drop t

public export
lift : Len ctx' => CoTerms ctx ctx' -> CoTerms (ctx :< ty) (ctx' :< ty)
lift sub = shift sub :< var Here

public export
restrict : CoTerms ctx' ctx'' -> ctx `Thins` ctx' -> CoTerms ctx ctx''
restrict [<] Empty = [<]
restrict (sub :< t) (Drop thin) = restrict sub thin
restrict (sub :< t) (Keep thin) = restrict sub thin :< t

public export
Base : (len : Len ctx') => ctx `Thins` ctx' -> CoTerms ctx ctx'
Base Empty = [<]
Base {len = S k} (Drop thin) = shift (Base thin)
Base {len = S k} (Keep thin) = lift (Base thin)

-- Substitution Operation ------------------------------------------------------

public export
subst : Len ctx' => FullTerm ty ctx -> CoTerms ctx ctx' -> FullTerm ty ctx'
public export
subst' : Len ctx' => CoTerm ty ctx -> CoTerms ctx ctx' -> FullTerm ty ctx'

subst (t `Over` thin) sub = subst' t (restrict sub thin)

subst' Var sub = index sub Here
subst' (Abs (MakeBound t (Drop Empty))) sub = abs (subst' t $ shift sub)
subst' (Abs (MakeBound t (Keep Empty))) sub = abs (subst' t $ lift sub)
subst' (App (MakePair t u _)) sub = app (subst t sub) (subst u sub)
subst' Zero sub = zero
subst' (Suc t) sub = suc (subst' t sub)
subst' (Rec (MakePair t (MakePair u v _ `Over` thin) _)) sub =
  rec (subst t sub) (subst u (restrict sub thin)) (subst v (restrict sub thin))

-- Initiality ------------------------------------------------------------------

toTerm' : CoTerm ty ctx -> ctx `Thins` ctx' -> Term ctx' ty
toTerm' Var thin = Var (index thin Here)
toTerm' (Abs (MakeBound t (Drop Empty))) thin = Abs (toTerm' t (Drop thin))
toTerm' (Abs (MakeBound t (Keep Empty))) thin = Abs (toTerm' t (Keep thin))
toTerm' (App (MakePair (t `Over` thin1) (u `Over` thin2) _)) thin =
  App (toTerm' t (thin . thin1)) (toTerm' u (thin . thin2))
toTerm' Zero thin = Zero
toTerm' (Suc t) thin = Suc (toTerm' t thin)
toTerm'
  (Rec
    (MakePair
      (t `Over` thin1)
      (MakePair (u `Over` thin2) (v `Over` thin3) _ `Over` thin') _))
  thin =
  Rec
    (toTerm' t (thin . thin1))
    (toTerm' u ((thin . thin') . thin2))
    (toTerm' v ((thin . thin') . thin3))

export
toTerm : FullTerm ty ctx -> Term ctx ty
toTerm (t `Over` thin) = toTerm' t thin

public export
toTerms : Len ctx' => CoTerms ctx ctx' -> Terms ctx' ctx
toTerms [<] = Base empty
toTerms (sub :< t) = toTerms sub :< toTerm t

export
Cast (FullTerm ty ctx) (Term ctx ty) where
  cast = toTerm

export
Len ctx' => Cast (CoTerms ctx ctx') (Terms ctx' ctx) where
  cast = toTerms

export
Len ctx => Cast (Term ctx ty) (FullTerm ty ctx) where
  cast (Var i) = Var `Over` point i
  cast (Abs t) = abs (cast t)
  cast (App {ty} t u) = app {ty} (cast t) (cast u)
  cast Zero = zero
  cast (Suc t) = suc (cast t)
  cast (Rec t u v) = rec (cast t) (cast u) (cast v)

-- Properties ------------------------------------------------------------------

wknToTerm' :
  (t : CoTerm ty ctx) ->
  (thin : ctx `Thins` ctx') ->
  (thin' : ctx' `Thins` ctx''') ->
  wkn (toTerm' t thin) thin' = toTerm' t (thin' . thin)
wknToTerm' Var thin thin' = cong Var (indexHomo thin' thin Here)
wknToTerm' (Abs (MakeBound t (Drop Empty))) thin thin' =
  cong Abs (wknToTerm' t (Drop thin) (Keep thin'))
wknToTerm' (Abs (MakeBound t (Keep Empty))) thin thin' =
  cong Abs (wknToTerm' t (Keep thin) (Keep thin'))
wknToTerm' (App (MakePair (t `Over` thin1) (u `Over` thin2) _)) thin thin' =
  rewrite sym $ assoc thin' thin thin1 in
  rewrite sym $ assoc thin' thin thin2 in
  cong2 App (wknToTerm' t (thin . thin1) thin') (wknToTerm' u (thin . thin2) thin')
wknToTerm' Zero thin thin' = Refl
wknToTerm' (Suc t) thin thin' = cong Suc (wknToTerm' t thin thin')
wknToTerm'
  (Rec
    (MakePair
      (t `Over` thin1)
      (MakePair (u `Over` thin2) (v `Over` thin3) _ `Over` thin'') _))
  thin
  thin' =
  rewrite sym $ assoc thin' thin thin1 in
  rewrite sym $ assoc (thin' . thin) thin'' thin2 in
  rewrite sym $ assoc thin'  thin (thin'' . thin2) in
  rewrite sym $ assoc thin thin'' thin2 in
  rewrite sym $ assoc (thin' . thin) thin'' thin3 in
  rewrite sym $ assoc thin'  thin (thin'' . thin3) in
  rewrite sym $ assoc thin thin'' thin3 in
  cong3 Rec
    (wknToTerm' t (thin . thin1) thin')
    (wknToTerm' u (thin . (thin'' . thin2)) thin')
    (wknToTerm' v (thin . (thin'' . thin3)) thin')

export
wknToTerm :
  (t : FullTerm ty ctx) ->
  (thin : ctx `Thins` ctx') ->
  wkn (toTerm t) thin = toTerm (wkn t thin)
wknToTerm (t `Over` thin') thin = wknToTerm' t thin' thin

export
toTermVar : Len ctx => (i : Elem ty ctx) -> toTerm (var i) = Var i
toTermVar i = cong Var $ indexPoint i

export
toTermApp :
  (t : FullTerm (ty ~> ty') ctx) ->
  (u : FullTerm ty ctx) ->
  toTerm (app t u) = App (toTerm t) (toTerm u)
toTermApp (t `Over` thin1) (u `Over` thin2) =
  cong2 App
    (cong (toTerm' t) $ irrelevantEq $ triangleCorrect (coprod thin1 thin2).left)
    (cong (toTerm' u) $ irrelevantEq $ triangleCorrect (coprod thin1 thin2).right)

indexShift :
  (sub : CoTerms ctx ctx') ->
  (i : Elem ty ctx) ->
  index (shift sub) i = drop (index sub i)
indexShift (sub :< t) Here = Refl
indexShift (sub :< t) (There i) = indexShift sub i

indexBase : (thin : [<ty] `Thins` ctx') -> index (Base thin) Here = Var `Over` thin
indexBase (Drop thin) = trans (indexShift (Base thin) Here) (cong drop (indexBase thin))
indexBase (Keep thin) = irrelevantEq $ cong ((Var `Over`) . Keep) $ emptyUnique empty thin

restrictShift :
  (sub : CoTerms ctx' ctx'') ->
  (thin : ctx `Thins` ctx') ->
  restrict (shift sub) thin = shift (restrict sub thin)
restrictShift [<] Empty = Refl
restrictShift (sub :< t) (Drop thin) = restrictShift sub thin
restrictShift (sub :< t) (Keep thin) = cong (:< drop t) (restrictShift sub thin)

restrictBase :
  (thin2 : ctx' `Thins` ctx'') ->
  (thin1 : ctx `Thins` ctx') ->
  CoDebruijn.restrict (Base thin2) thin1 = Base (thin2 . thin1)
restrictBase Empty Empty = Refl
restrictBase (Drop thin2) thin1 =
  trans
    (restrictShift (Base thin2) thin1)
    (cong shift $ restrictBase thin2 thin1)
restrictBase (Keep thin2) (Drop thin1) =
  trans
    (restrictShift (Base thin2) thin1)
    (cong shift $ restrictBase thin2 thin1)
restrictBase (Keep thin2) (Keep thin1) =
  cong (:< (Var `Over` point Here)) $
  trans
    (restrictShift (Base thin2) thin1)
    (cong shift $ restrictBase thin2 thin1)

substBase :
  (t : CoTerm ty ctx) ->
  (thin : ctx `Thins` ctx') ->
  subst' t (Base thin) = t `Over` thin
substBase Var thin = indexBase thin
substBase (Abs (MakeBound t (Drop Empty))) thin =
  Calc $
    |~ map Abs (MkBound (S Z) (subst' t (shift $ Base thin)))
    ~~ map Abs (MkBound (S Z) (t `Over` Drop thin))
      ...(cong (map Abs . MkBound (S Z)) $ substBase t (Drop thin))
    ~~ map Abs (MakeBound t (Drop Empty) `Over` thin)
      ...(Refl)
    ~~ (Abs (MakeBound t (Drop Empty)) `Over` thin)
      ...(Refl)
substBase (Abs (MakeBound t (Keep Empty))) thin = 
  Calc $
    |~ map Abs (MkBound (S Z) (subst' t (lift $ Base thin)))
    ~~ map Abs (MkBound (S Z) (t `Over` Keep thin))
      ...(cong (map Abs . MkBound (S Z)) $ substBase t (Keep thin))
    ~~ map Abs (MakeBound t (Keep Empty) `Over` thin)
      ...(Refl)
    ~~ (Abs (MakeBound t (Keep Empty)) `Over` thin)
      ...(Refl)
substBase (App (MakePair (t `Over` thin1) (u `Over` thin2) cover)) thin =
  rewrite restrictBase thin thin1 in
  rewrite restrictBase thin thin2 in
  rewrite substBase t (thin . thin1) in
  rewrite substBase u (thin . thin2) in
  rewrite coprodEta thin cover in
  Refl
substBase Zero thin = cong (Zero `Over`) $ irrelevantEq $ emptyUnique empty thin
substBase (Suc t) thin = cong (map Suc) $ substBase t thin
substBase
  (Rec (MakePair
      (t `Over` thin1)
      (MakePair
        (u `Over` thin2)
        (v `Over` thin3)
        cover'
      `Over` thin')
      cover))
  thin =
  rewrite restrictBase thin thin1 in
  rewrite restrictBase thin thin' in
  rewrite restrictBase (thin . thin') thin2 in
  rewrite restrictBase (thin . thin') thin3 in
  rewrite substBase t (thin . thin1) in
  rewrite substBase u ((thin . thin') . thin2) in
  rewrite substBase v ((thin . thin') . thin3) in
  rewrite coprodEta (thin . thin') cover' in
  rewrite coprodEta thin cover in
  Refl

export
substId : (t : FullTerm ty ctx) -> subst t (Base Thinning.id) = t
substId (t `Over` thin) =
  Calc $
    |~ subst' t (restrict (Base id) thin)
    ~~ subst' t (Base $ id . thin)
      ...(cong (subst' t) $ restrictBase id thin)
    ~~ subst' t (Base thin)
      ...(cong (subst' t . Base) $ identityLeft thin)
    ~~ (t `Over` thin)
      ...(substBase t thin)
