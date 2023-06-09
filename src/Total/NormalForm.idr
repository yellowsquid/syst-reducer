module Total.NormalForm

import Total.LogRel
import Total.Reduction
import Total.Term
import Total.Term.CoDebruijn

%prefix_record_projections off

public export
data Neutral' : CoTerm ty ctx -> Type
public export
data Normal' : CoTerm ty ctx -> Type

public export
data Neutral : FullTerm ty ctx -> Type

public export
data Normal : FullTerm ty ctx -> Type

data Neutral' where
  Var : Neutral' Var
  App : Neutral t -> Normal u -> Neutral' (App (MakePair t u cover))
  Rec :
    Neutral t ->
    Normal u ->
    Normal v ->
    Neutral' (Rec (MakePair t (MakePair u v cover1 `Over` thin) cover2))

data Normal' where
  Ntrl : Neutral' t -> Normal' t
  Abs : Normal' t -> Normal' (Abs (MakeBound t thin))
  Zero : Normal' Zero
  Suc : Normal' t -> Normal' (Suc t)

data Neutral where
  WrapNe : Neutral' t -> Neutral (t `Over` thin)

data Normal where
  WrapNf : Normal' t -> Normal (t `Over` thin)

%name Neutral n, m, k
%name Normal n, m, k
%name Neutral' n, m, k
%name Normal' n, m, k

public export
record NormalForm (0 t : FullTerm ty ctx) where
  constructor MkNf
  term : FullTerm ty ctx
  0 steps : toTerm t >= toTerm term
  0 normal : Normal term

%name NormalForm nf

-- Strong Normalization Proof --------------------------------------------------

abs : Normal t -> Normal (abs t)

app : Neutral t -> Normal u -> Neutral (app t u)

suc : Normal t -> Normal (suc t)

rec : Neutral t -> Normal u -> Normal v -> Neutral (rec t u v)

invApp : Normal' (App x) -> Neutral' (App x)
invApp (Ntrl n) = n

invRec : Normal' (Rec x) -> Neutral' (Rec x)
invRec (Ntrl n) = n

invSuc : Normal' (Suc t) -> Normal' t
invSuc (Suc n) = n

wknNe : Neutral t -> Neutral (wkn t thin)
wknNe (WrapNe n) = WrapNe n

wknNf : Normal t -> Normal (wkn t thin)
wknNf (WrapNf n) = WrapNf n

backStepsNf : NormalForm t -> (0 _ : toTerm u >= toTerm t) -> NormalForm u
backStepsNf nf steps = MkNf nf.term (steps ++ nf.steps) nf.normal

backStepsRel :
  {ty : Ty} ->
  {0 t, u : FullTerm ty ctx} ->
  LogRel (\t => NormalForm t) t ->
  (0 _ : toTerm u >= toTerm t) ->
  LogRel (\t => NormalForm t) u
backStepsRel =
  preserve {R = flip (>=) `on` toTerm}
    (MkPresHelper
      (\t, u, thin, v, steps =>
        ?appCong1Steps)
      backStepsNf)

ntrlRel : {ty : Ty} -> {t : FullTerm ty ctx} -> (0 _ : Neutral t) -> LogRel (\t => NormalForm t) t
ntrlRel {ty = N} (WrapNe n) = MkNf t [<] (WrapNf (Ntrl n))
ntrlRel {ty = ty ~> ty'} (WrapNe {thin = thin'} n) =
  ( MkNf t [<] (WrapNf (Ntrl n))
  , \thin, u, rel =>
    backStepsRel
      (ntrlRel (app (wknNe {thin} (WrapNe {thin = thin'} n)) (escape rel).normal))
      ?appCong2Steps
  )

recNf'' :
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  {u : FullTerm ty ctx} ->
  {v : FullTerm (ty ~> ty) ctx} ->
  (t : CoTerm N ctx') ->
  (thin : ctx' `Thins` ctx) ->
  (0 n : Normal' t) ->
  LogRel (\t => NormalForm t) u ->
  LogRel (\t => NormalForm t) v ->
  LogRel (\t => NormalForm t) (rec (t `Over` thin) u v)
recNf'' Zero thin n relU relV =
  backStepsRel relU [<?recZero]
recNf'' (Suc t) thin n relU relV =
  let rec = recNf'' t thin (invSuc n) relU relV in
  backStepsRel (snd relV id _ rec) [<?recSuc]
recNf'' t@Var thin n relU relV =
  let 0 neT = WrapNe {thin} Var in
  let nfU = escape relU in
  let nfV = escape {ty = ty ~> ty} relV in
  backStepsRel
    (ntrlRel (rec neT nfU.normal nfV.normal))
    ?stepsUandV
recNf'' t@(App _) thin n relU relV =
  let 0 neT = WrapNe {thin} (invApp n) in
  let nfU = escape relU in
  let nfV = escape {ty = ty ~> ty} relV in
  backStepsRel
    (ntrlRel (rec neT nfU.normal nfV.normal))
    ?stepsUandV'
recNf'' t@(Rec _) thin n relU relV =
  let 0 neT = WrapNe {thin} (invRec n) in
  let nfU = escape relU in
  let nfV = escape {ty = ty ~> ty} relV in
  backStepsRel
    (ntrlRel (rec neT nfU.normal nfV.normal))
    ?stepsUandV''

recNf' :
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  {u : FullTerm ty ctx} ->
  {v : FullTerm (ty ~> ty) ctx} ->
  (t : FullTerm N ctx) ->
  (0 n : Normal t) ->
  LogRel (\t => NormalForm t) u ->
  LogRel (\t => NormalForm t) v ->
  LogRel (\t => NormalForm t) (rec t u v)
recNf' (t `Over` thin) (WrapNf n) = recNf'' t thin n

recNf :
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  {0 t : FullTerm N ctx} ->
  {u : FullTerm ty ctx} ->
  {v : FullTerm (ty ~> ty) ctx} ->
  NormalForm t ->
  LogRel (\t => NormalForm t) u ->
  LogRel (\t => NormalForm t) v ->
  LogRel (\t => NormalForm t) (rec t u v)
recNf nf relU relV =
  backStepsRel
    (recNf' nf.term nf.normal relU relV)
    ?recCong1Steps

helper : ValidHelper (\t => NormalForm t)
helper = MkValidHelper
  { var = \i => ntrlRel (WrapNe Var)
  , abs = \rel =>
    let nf = escape rel in
    MkNf (abs nf.term) ?absCongSteps (abs nf.normal)
  , zero = MkNf zero [<] (WrapNf Zero)
  , suc = \nf => MkNf (suc nf.term) ?sucCongSteps (suc nf.normal)
  , rec = recNf
  , step = \nf, step => backStepsNf nf [<step]
  , wkn = \nf, thin => MkNf (wkn nf.term thin) ?wknSteps (wknNf nf.normal)
  }

export
normalize : {ctx : SnocList Ty} -> {ty : Ty} -> (t : FullTerm ty ctx) -> NormalForm t
normalize = allRel helper
