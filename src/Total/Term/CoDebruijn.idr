module Total.Term.CoDebruijn

import public Data.SnocList.Elem
import public Thinning
import Syntax.PreorderReasoning
import Total.Term

%prefix_record_projections off

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

export
var : Len ctx => Elem ty ctx -> FullTerm ty ctx
var i = Var `Over` point i

export
abs : FullTerm ty' (ctx :< ty) -> FullTerm (ty ~> ty') ctx
abs = map Abs . MkBound (S Z)

export
app : {ty : Ty} -> FullTerm (ty ~> ty') ctx -> FullTerm ty ctx -> FullTerm ty' ctx
app t u = map App (MkPair t u)

export
zero : Len ctx => FullTerm N ctx
zero = Zero `Over` empty

export
suc : FullTerm N ctx -> FullTerm N ctx
suc = map Suc

export
rec : FullTerm N ctx -> FullTerm ty ctx -> FullTerm (ty ~> ty) ctx -> FullTerm ty ctx
rec t u v = map Rec $ MkPair t (MkPair u v)

export
wkn : FullTerm ty ctx -> ctx `Thins` ctx' -> FullTerm ty ctx'
wkn (t `Over` thin) thin' = t `Over` thin' . thin

public export
data CoTerms : SnocList Ty -> SnocList Ty -> Type where
  Base : ctx `Thins` ctx' -> CoTerms ctx ctx'
  (:<) : CoTerms ctx ctx' -> FullTerm ty ctx' -> CoTerms (ctx :< ty) ctx'

%name CoTerms sub

export
shift : CoTerms ctx ctx' -> CoTerms ctx (ctx' :< ty)
shift (Base thin) = Base (Drop thin)
shift (sub :< (t `Over` thin)) = shift sub :< (t `Over` Drop thin)

export
lift : Len ctx' => CoTerms ctx ctx' -> CoTerms (ctx :< ty) (ctx' :< ty)
lift sub = shift sub :< var Here

export
restrict : CoTerms ctx' ctx'' -> ctx `Thins` ctx' -> CoTerms ctx ctx''
restrict (Base thin') thin = Base (thin' . thin)
restrict (sub :< t) (Drop thin) = restrict sub thin
restrict (sub :< t) (Keep thin) = restrict sub thin :< t

export
subst : Len ctx' => FullTerm ty ctx -> CoTerms ctx ctx' -> FullTerm ty ctx'
subst' : Len ctx' => CoTerm ty ctx -> CoTerms ctx ctx' -> FullTerm ty ctx'

subst (t `Over` thin) sub = subst' t (restrict sub thin)

subst' t (Base thin) = t `Over` thin
subst' Var (sub :< t) = t
subst' (Abs (MakeBound t (Drop Empty))) sub@(_ :< _) = abs (subst' t $ shift sub)
subst' (Abs (MakeBound t (Keep Empty))) sub@(_ :< _) = abs (subst' t $ lift sub)
subst' (App (MakePair t u _)) sub@(_ :< _) = app (subst t sub) (subst u sub)
subst' (Suc t) sub@(_ :< _) = suc (subst' t sub)
subst' (Rec (MakePair t (MakePair u v _ `Over` thin) _)) sub@(_ :< _) =
  rec (subst t sub) (subst u (restrict sub thin)) (subst v (restrict sub thin))

toTerm : CoTerm ty ctx -> ctx `Thins` ctx' -> Term ctx' ty
toTerm Var thin = Var (index thin Here)
toTerm (Abs (MakeBound t (Drop Empty))) thin = Abs (toTerm t (Drop thin))
toTerm (Abs (MakeBound t (Keep Empty))) thin = Abs (toTerm t (Keep thin))
toTerm (App (MakePair (t `Over` thin1) (u `Over` thin2) _)) thin =
  App (toTerm t (thin . thin1)) (toTerm u (thin . thin2))
toTerm Zero thin = Zero
toTerm (Suc t) thin = Suc (toTerm t thin)
toTerm
  (Rec
    (MakePair
      (t `Over` thin1)
      (MakePair (u `Over` thin2) (v `Over` thin3) _ `Over` thin') _))
  thin =
  Rec
    (toTerm t (thin . thin1))
    (toTerm u ((thin . thin') . thin2))
    (toTerm v ((thin . thin') . thin3))

export
Cast (FullTerm ty ctx) (Term ctx ty) where
  cast (t `Over` thin) = toTerm t thin
