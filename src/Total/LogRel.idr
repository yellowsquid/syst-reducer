module Total.LogRel

import Syntax.PreorderReasoning
import Total.Reduction
import Total.Term

%prefix_record_projections off

public export
LogRel :
  {ctx : SnocList Ty} ->
  (P : {ctx, ty : _} -> Term ctx ty -> Type) ->
  {ty : Ty} ->
  (t : Term ctx ty) ->
  Type
LogRel p {ty = N} t = p t
LogRel p {ty = ty ~> ty'} t =
  (p t,
   {ctx' : SnocList Ty} ->
   (thin : ctx `Thins` ctx') ->
   (u : Term ctx' ty) ->
   LogRel p u ->
   LogRel p (App (wkn t thin) u))

export
escape :
  {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  {ty : Ty} ->
  {0 t : Term ctx ty} ->
  LogRel P t ->
  P t
escape {ty = N} pt = pt
escape {ty = ty ~> ty'} (pt, app) = pt

public export
record PreserveHelper
  (P : {ctx, ty : _} -> Term ctx ty -> Type)
  (R : {ctx, ty : _} -> Term ctx ty -> Term ctx ty -> Type) where
  constructor MkPresHelper
  app :
    {0 ctx : SnocList Ty} ->
    {ty, ty' : Ty} ->
    {0 t, u : Term ctx (ty ~> ty')} ->
    {ctx' : SnocList Ty} ->
    (thin : ctx `Thins` ctx') ->
    (v : Term ctx' ty) ->
    R t u ->
    R (App (wkn t thin) v) (App (wkn u thin) v)
  pres :
    {0 ctx : SnocList Ty} ->
    {ty : Ty} ->
    {0 t, u : Term ctx ty} ->
    P t ->
    (0 _ : R t u) ->
    P u

%name PreserveHelper help

export
backStepHelper :
  {0 P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  (forall ctx, ty. {0 t, u : Term ctx ty} -> P t -> (0 _ : u > t) -> P u) ->
  PreserveHelper P (flip (>))
backStepHelper pres =
  MkPresHelper
    (\thin, v, step => AppCong1 (wknStep step))
    pres

export
preserve :
  {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  {R : {ctx, ty : _} -> Term ctx ty -> Term ctx ty -> Type} ->
  {ty : Ty} ->
  {0 t, u : Term ctx ty} ->
  PreserveHelper P R ->
  LogRel P t ->
  (0 _ : R t u) ->
  LogRel P u
preserve help {ty = N} pt prf = help.pres pt prf
preserve help {ty = ty ~> ty'} (pt, app) prf =
  (help.pres pt prf, \thin, v, rel => preserve help (app thin v rel) (help.app thin v prf))

data AllLogRel : (P : {ctx, ty : _} -> Term ctx ty -> Type) -> Terms ctx' ctx -> Type where
  Base :
    {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
    {0 thin : ctx `Thins` ctx'} ->
    AllLogRel P (Base thin)
  (:<) :
    {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
    AllLogRel P sub ->
    LogRel P t ->
    AllLogRel P (sub :< t)

%name AllLogRel allRels

index :
  {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  ((i : Elem ty ctx') -> LogRel P (Var i)) ->
  {sub : Terms ctx' ctx} ->
  AllLogRel P sub ->
  (i : Elem ty ctx) ->
  LogRel P (index sub i)
index f Base i = f (index _ i)
index f (allRels :< rel) Here = rel
index f (allRels :< rel) (There i) = index f allRels i

Valid :
  (P : {ctx, ty : _} -> Term ctx ty -> Type) ->
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  (t : Term ctx ty) ->
  Type
Valid p t =
  {ctx' : SnocList Ty} ->
  (sub : Terms ctx' ctx) ->
  (allRel : AllLogRel p sub) ->
  LogRel p (subst t sub)

public export
record ValidHelper (P : {ctx, ty : _} -> Term ctx ty -> Type) where
  constructor MkValidHelper
  var : forall ctx. {ty : Ty} -> (i : Elem ty ctx) -> LogRel P (Var i)
  abs : forall ctx, ty. {ty' : Ty} -> {0 t : Term (ctx :< ty) ty'} -> LogRel P t -> P (Abs t)
  zero : forall ctx. P {ctx} Zero
  suc : forall ctx. {0 t : Term ctx N} -> P t -> P (Suc t)
  rec :
    {ctx : SnocList Ty} ->
    {ty : Ty} ->
    {0 t : Term ctx N} ->
    {u : Term ctx ty} ->
    {v : Term ctx (ty ~> ty)} ->
    LogRel P t ->
    LogRel P u ->
    LogRel P v ->
    LogRel P (Rec t u v)
  step : forall ctx, ty. {0 t, u : Term ctx ty} -> P t -> (0 _ : u > t) -> P u
  wkn : forall ctx, ctx', ty.
    {0 t : Term ctx ty} ->
    P t ->
    (thin : ctx `Thins` ctx') ->
    P (wkn t thin)

%name ValidHelper help

wknRel :
  {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  ValidHelper P ->
  {ty : Ty} ->
  {0 t : Term ctx ty} ->
  LogRel P t ->
  (thin : ctx `Thins` ctx') ->
  LogRel P (wkn t thin)
wknRel help {ty = N} pt thin = help.wkn pt thin
wknRel help {ty = ty ~> ty'} (pt, app) thin =
  ( help.wkn pt thin
  , \thin', u, rel => rewrite wknHomo t thin thin' in app (thin' . thin) u rel
  )

wknAllRel :
  {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  ValidHelper P ->
  {ctx : SnocList Ty} ->
  {sub : Terms ctx' ctx} ->
  AllLogRel P sub ->
  (thin : ctx' `Thins` ctx'') ->
  AllLogRel P (wknAll sub thin)
wknAllRel help Base thin = Base
wknAllRel help (allRels :< rel) thin = wknAllRel help allRels thin :< wknRel help rel thin

export
allValid :
  {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  ValidHelper P ->
  (t : Term ctx ty) ->
  Valid P t
allValid help (Var i) sub allRels = index help.var allRels i
allValid help (Abs t) sub allRels =
  let valid = allValid help t in
  (let
      rec =
        valid
          (wknAll sub (Drop id) :< Var Here)
          (wknAllRel help allRels (Drop id) :< help.var Here)
    in
      help.abs rec
  , \thin, u, rel =>
    let
      eq :
        (subst
          (wkn (subst t (wknAll sub (Drop Thinning.id) :< Var Here)) (Keep thin))
          (Base Thinning.id :< u) =
         subst t (wknAll sub thin :< u))
      eq =
        Calc $
          |~ subst (wkn (subst t (wknAll sub (Drop id) :< Var Here)) (Keep thin)) (Base id :< u)
          ~~ subst (subst t (wknAll sub (Drop id) :< Var Here)) (restrict (Base id :< u) (Keep thin))
            ...(substWkn (subst t (wknAll sub (Drop id) :< Var Here)) (Keep thin) (Base id :< u))
          ~~ subst (subst t (wknAll sub (Drop id) :< Var Here)) (Base thin :< u)
            ...(cong (subst (subst t (wknAll sub (Drop id) :< Var Here)) . (:< u) . Base) $ identityLeft thin)
          ~~ subst t ((Base thin :< u) . wknAll sub (Drop id) :< u)
            ...(substHomo t (wknAll sub (Drop id) :< Var Here) (Base thin :< u))
          ~~ subst t (Base (thin . id) . sub :< u)
            ...(cong (subst t . (:< u)) $ compWknAll sub (Base thin :< u) (Drop id))
          ~~ subst t (Base thin . sub :< u)
            ...(cong (subst t . (:< u) . (. sub) . Base) $ identityRight thin)
          ~~ subst t (wknAll sub thin :< u)
            ...(cong (subst t . (:< u)) $ baseComp thin sub)
    in
      preserve
        (backStepHelper help.step)
        (valid (wknAll sub thin :< u) (wknAllRel help allRels thin :< rel))
        (replace {p = (App (wkn (subst (Abs t) sub) thin) u >)}
          eq
          (AppBeta (length _)))
  )
allValid help (App t u) sub allRels =
  let (pt, app) = allValid help t sub allRels in
  let rel = allValid help u sub allRels in
  rewrite sym $ wknId (subst t sub) in
    app id (subst u sub) rel
allValid help Zero sub allRels = help.zero
allValid help (Suc t) sub allRels =
  let pt = allValid help t sub allRels in
  help.suc pt
allValid help (Rec t u v) sub allRels =
  let relt = allValid help t sub allRels in
  let relu = allValid help u sub allRels in
  let relv = allValid help v sub allRels in
  help.rec relt relu relv

export
allRel :
  {P : {ctx, ty : _} -> Term ctx ty -> Type} ->
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  ValidHelper P ->
  (t : Term ctx ty) ->
  P t
allRel help t =
  rewrite sym $ substId t in escape (allValid help t (Base id) Base)
