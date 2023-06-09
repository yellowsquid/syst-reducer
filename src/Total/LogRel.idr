module Total.LogRel

import Data.Singleton
import Syntax.PreorderReasoning
import Total.Reduction
import Total.Term
import Total.Term.CoDebruijn

%prefix_record_projections off

public export
LogRel :
  {ctx : SnocList Ty} ->
  (P : {ctx, ty : _} -> FullTerm ty ctx -> Type) ->
  {ty : Ty} ->
  (t : FullTerm ty ctx) ->
  Type
LogRel p {ty = N} t = p t
LogRel p {ty = ty ~> ty'} t =
  (p t,
   {ctx' : SnocList Ty} ->
   (thin : ctx `Thins` ctx') ->
   (u : FullTerm ty ctx') ->
   LogRel p u ->
   LogRel p (app (wkn t thin) u))

export
escape :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  {ty : Ty} ->
  {0 t : FullTerm ty ctx} ->
  LogRel P t ->
  P t
escape {ty = N} pt = pt
escape {ty = ty ~> ty'} (pt, app) = pt

public export
record PreserveHelper
  (P : {ctx, ty : _} -> FullTerm ty ctx -> Type)
  (R : {ctx, ty : _} -> FullTerm ty ctx -> FullTerm ty ctx -> Type) where
  constructor MkPresHelper
  0 app :
    {ctx : SnocList Ty} ->
    {ty, ty' : Ty} ->
    (t, u : FullTerm (ty ~> ty') ctx) ->
    {ctx' : SnocList Ty} ->
    (thin : ctx `Thins` ctx') ->
    (v : FullTerm ty ctx') ->
    R t u ->
    R (app (wkn t thin) v) (app (wkn u thin) v)
  pres :
    {0 ctx : SnocList Ty} ->
    {ty : Ty} ->
    {0 t, u : FullTerm ty ctx} ->
    P t ->
    (0 _ : R t u) ->
    P u

%name PreserveHelper help

export
backStepHelper :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  (forall ctx, ty. {0 t, u : FullTerm ty ctx} -> P t -> (0 _ : toTerm u > toTerm t) -> P u) ->
  PreserveHelper P (flip (>) `on` CoDebruijn.toTerm)
backStepHelper pres =
  MkPresHelper
    (\t, u, thin, v, step =>
      rewrite toTermApp (wkn u thin) v in
      rewrite toTermApp (wkn t thin) v in
      rewrite sym $ wknToTerm t thin in
      rewrite sym $ wknToTerm u thin in
      AppCong1 (wknStep step))
    pres

export
preserve :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  {0 R : {ctx, ty : _} -> FullTerm ty ctx -> FullTerm ty ctx -> Type} ->
  {ty : Ty} ->
  {0 t, u : FullTerm ty ctx} ->
  PreserveHelper P R ->
  LogRel P t ->
  (0 _ : R t u) ->
  LogRel P u
preserve help {ty = N} pt prf = help.pres pt prf
preserve help {ty = ty ~> ty'} (pt, app) prf =
  (help.pres pt prf, \thin, v, rel => preserve help (app thin v rel) (help.app _ _ thin v prf))

data AllLogRel : (P : {ctx, ty : _} -> FullTerm ty ctx -> Type) -> CoTerms ctx ctx' -> Type where
  Lin :
    {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
    AllLogRel P [<]
  (:<) :
    {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
    AllLogRel P sub ->
    LogRel P t ->
    AllLogRel P (sub :< t)

%name AllLogRel allRels

index :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ((i : Elem ty ctx') -> LogRel P (var i)) ->
  {sub : CoTerms ctx ctx'} ->
  AllLogRel P sub ->
  (i : Elem ty ctx) ->
  LogRel P (index sub i)
index f (allRels :< rel) Here = rel
index f (allRels :< rel) (There i) = index f allRels i

restrict :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  {0 sub : CoTerms ctx' ctx''} ->
  AllLogRel P sub ->
  (thin : ctx `Thins` ctx') ->
  AllLogRel P (restrict sub thin)
restrict [<] Empty = [<]
restrict (allRels :< rel) (Drop thin) = restrict allRels thin
restrict (allRels :< rel) (Keep thin) = restrict allRels thin :< rel

Valid :
  (P : {ctx, ty : _} -> FullTerm ty ctx -> Type) ->
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  (t : FullTerm ty ctx) ->
  Type
Valid p t =
  {ctx' : SnocList Ty} ->
  (sub : CoTerms ctx ctx') ->
  (allRel : AllLogRel p sub) ->
  LogRel p (subst t sub)

public export
record ValidHelper (P : {ctx, ty : _} -> FullTerm ty ctx -> Type) where
  constructor MkValidHelper
  var : forall ctx. Len ctx => {ty : Ty} -> (i : Elem ty ctx) -> LogRel P (var i)
  abs : forall ctx, ty. {ty' : Ty} -> {0 t : FullTerm ty' (ctx :< ty)} -> LogRel P t -> P (abs t)
  zero : forall ctx. Len ctx => P {ctx} zero
  suc : forall ctx. {0 t : FullTerm N ctx} -> P t -> P (suc t)
  rec :
    {ctx : SnocList Ty} ->
    {ty : Ty} ->
    {0 t : FullTerm N ctx} ->
    {u : FullTerm ty ctx} ->
    {v : FullTerm (ty ~> ty) ctx} ->
    LogRel P t ->
    LogRel P u ->
    LogRel P v ->
    LogRel P (rec t u v)
  step : forall ctx, ty. {0 t, u : FullTerm ty ctx} -> P t -> (0 _ : toTerm u > toTerm t) -> P u
  wkn : forall ctx, ctx', ty.
    {0 t : FullTerm ty ctx} ->
    P t ->
    (thin : ctx `Thins` ctx') ->
    P (wkn t thin)

%name ValidHelper help

wknRel :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ValidHelper P ->
  {ty : Ty} ->
  {0 t : FullTerm ty ctx} ->
  LogRel P t ->
  (thin : ctx `Thins` ctx') ->
  LogRel P (wkn t thin)
wknRel help {ty = N} pt thin = help.wkn pt thin
wknRel help {ty = ty ~> ty'} (pt, app) thin =
  ( help.wkn pt thin
  , \thin', u, rel =>
    rewrite wknHomo t thin' thin in
    app (thin' . thin) u rel
  )

wknAllRel :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ValidHelper P ->
  {ctx : SnocList Ty} ->
  {sub : CoTerms ctx ctx'} ->
  AllLogRel P sub ->
  (thin : ctx' `Thins` ctx'') ->
  AllLogRel P (wknAll sub thin)
wknAllRel help [<] thin = [<]
wknAllRel help (allRels :< rel) thin = wknAllRel help allRels thin :< wknRel help rel thin

shiftRel :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ValidHelper P ->
  {ctx, ctx' : SnocList Ty} ->
  {sub : CoTerms ctx ctx'} ->
  AllLogRel P sub ->
  AllLogRel P (shift {ty} sub)
shiftRel help [<] = [<]
shiftRel help (allRels :< rel) =
  shiftRel help allRels :<
  replace {p = LogRel P} (sym $ dropIsWkn _) (wknRel help rel (Drop id))

liftRel :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ValidHelper P ->
  {ctx, ctx' : SnocList Ty} ->
  {ty : Ty} ->
  {sub : CoTerms ctx ctx'} ->
  AllLogRel P sub ->
  AllLogRel P (lift {ty} sub)
liftRel help allRels = shiftRel help allRels :< help.var Here

absValid :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ValidHelper P ->
  {ctx : SnocList Ty} ->
  {ty, ty' : Ty} ->
  (t : CoTerm ty' (ctx ++ used)) ->
  (thin : used `Thins` [<ty]) ->
  (valid : {ctx' : SnocList Ty} ->
    (sub : CoTerms (ctx ++ used) ctx') ->
    AllLogRel P sub ->
    LogRel P (subst' t sub)) ->
  {ctx' : SnocList Ty} ->
  (sub : CoTerms ctx ctx') ->
  AllLogRel P sub ->
  LogRel P (subst' (Abs (MakeBound t thin)) sub)
absValid help t (Drop Empty) valid sub allRels =
  ( help.abs (valid (shift sub) (shiftRel help allRels))
  , \thin, u, rel =>
    preserve
      (backStepHelper help.step)
      (valid (wknAll sub thin) (wknAllRel help allRels thin))
      ?betaStep
  )
absValid help t (Keep Empty) valid sub allRels =
  ( help.abs (valid (lift sub) (liftRel help allRels))
  , \thin, u, rel =>
    preserve (backStepHelper help.step)
      (valid (wknAll sub thin :< u) (wknAllRel help allRels thin :< rel))
      ?betaStep'
  )

export
allValid :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ValidHelper P ->
  (s : Singleton ctx) =>
  {ty : Ty} ->
  (t : FullTerm ty ctx) ->
  Valid P t
allValid' :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  ValidHelper P ->
  (s : Singleton ctx) =>
  {ty : Ty} ->
  (t : CoTerm ty ctx) ->
  {ctx' : SnocList Ty} ->
  (sub : CoTerms ctx ctx') ->
  AllLogRel P sub ->
  LogRel P (subst' t sub)

allValid help (t `Over` thin) sub allRels =
  allValid' help t (restrict sub thin) (restrict allRels thin)

allValid' help Var sub allRels = index help.var allRels Here
allValid' help {s = Val ctx} (Abs {ty, ty'} (MakeBound t thin)) sub allRels =
  let s' = [| Val ctx ++ retractSingleton (Val [<ty]) thin |] in
  absValid help t thin (allValid' help t) sub allRels
allValid' help (App (MakePair t u _)) sub allRels =
  let (pt, app) = allValid help t sub allRels in
  let rel = allValid help u sub allRels in
  rewrite sym $ wknId (subst t sub) in
  app id (subst u sub) rel
allValid' help Zero sub allRels = help.zero
allValid' help (Suc t) sub allRels =
  let pt = allValid' help t sub allRels in
  help.suc pt
allValid' help (Rec (MakePair t (MakePair u v _ `Over` thin) _)) sub allRels =
  let relT = allValid help t sub allRels in
  let relU = allValid help u (restrict sub thin) (restrict allRels thin) in
  let relV = allValid help v (restrict sub thin) (restrict allRels thin) in
  help.rec relT relU relV

-- -- allValid help (Var i) sub allRels = index help.var allRels i
-- -- allValid help (Abs t) sub allRels =
-- --   let valid = allValid help t in
-- --   (let
-- --       rec =
-- --         valid
-- --           (wknAll sub (Drop id) :< Var Here)
-- --           (wknAllRel help allRels (Drop id) :< help.var Here)
-- --     in
-- --       help.abs rec
-- --   , \thin, u, rel =>
-- --     let
-- --       eq :
-- --         (subst
-- --           (wkn (subst t (wknAll sub (Drop Thinning.id) :< Var Here)) (Keep thin))
-- --           (Base Thinning.id :< u) =
-- --          subst t (wknAll sub thin :< u))
-- --       eq =
-- --         Calc $
-- --           |~ subst (wkn (subst t (wknAll sub (Drop id) :< Var Here)) (Keep thin)) (Base id :< u)
-- --           ~~ subst (subst t (wknAll sub (Drop id) :< Var Here)) (restrict (Base id :< u) (Keep thin))
-- --             ...(substWkn (subst t (wknAll sub (Drop id) :< Var Here)) (Keep thin) (Base id :< u))
-- --           ~~ subst (subst t (wknAll sub (Drop id) :< Var Here)) (Base thin :< u)
-- --             ...(cong (subst (subst t (wknAll sub (Drop id) :< Var Here)) . (:< u) . Base) $ identityLeft thin)
-- --           ~~ subst t ((Base thin :< u) . wknAll sub (Drop id) :< u)
-- --             ...(substHomo t (wknAll sub (Drop id) :< Var Here) (Base thin :< u))
-- --           ~~ subst t (Base (thin . id) . sub :< u)
-- --             ...(cong (subst t . (:< u)) $ compWknAll sub (Base thin :< u) (Drop id))
-- --           ~~ subst t (Base thin . sub :< u)
-- --             ...(cong (subst t . (:< u) . (. sub) . Base) $ identityRight thin)
-- --           ~~ subst t (wknAll sub thin :< u)
-- --             ...(cong (subst t . (:< u)) $ baseComp thin sub)
-- --     in
-- --       preserve
-- --         (backStepHelper help.step)
-- --         (valid (wknAll sub thin :< u) (wknAllRel help allRels thin :< rel))
-- --         (replace {p = (App (wkn (subst (Abs t) sub) thin) u >)}
-- --           eq
-- --           (AppBeta (length _)))
-- --   )
-- -- allValid help (App t u) sub allRels =
-- --   let (pt, app) = allValid help t sub allRels in
-- --   let rel = allValid help u sub allRels in
-- --   rewrite sym $ wknId (subst t sub) in
-- --     app id (subst u sub) rel
-- -- allValid help Zero sub allRels = help.zero
-- -- allValid help (Suc t) sub allRels =
-- --   let pt = allValid help t sub allRels in
-- --   help.suc pt
-- -- allValid help (Rec t u v) sub allRels =
-- --   let relt = allValid help t sub allRels in
-- --   let relu = allValid help u sub allRels in
-- --   let relv = allValid help v sub allRels in
-- --   help.rec relt relu relv

idRel :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  {ctx : SnocList Ty} ->
  ValidHelper P ->
  AllLogRel P {ctx} (Base Thinning.id)
idRel help {ctx = [<]} = [<]
idRel help {ctx = ctx :< ty} = liftRel help (idRel help)

export
allRel :
  {0 P : {ctx, ty : _} -> FullTerm ty ctx -> Type} ->
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  ValidHelper P ->
  (t : FullTerm ty ctx) ->
  P t
allRel help t =
  rewrite sym $ substId t in
  escape {P} $
  allValid help @{Val ctx} t (Base id) (idRel help)
