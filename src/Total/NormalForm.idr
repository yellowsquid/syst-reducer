module Total.NormalForm

import Total.LogRel
import Total.Reduction
import Total.Term

%prefix_record_projections off

public export
data Neutral : Term ctx ty -> Type
public export
data Normal : Term ctx ty -> Type

data Neutral where
  Var : Neutral (Var i)
  App : Neutral t -> Normal u -> Neutral (App t u)
  Rec : Neutral t -> Normal u -> Normal v -> Neutral (Rec t u v)

data Normal where
  Ntrl : Neutral t -> Normal t
  Abs : Normal t -> Normal (Abs t)
  Zero : Normal Zero
  Suc : Normal t -> Normal (Suc t)

%name Neutral n, m, k
%name Normal n, m, k

public export
record NormalForm (0 t : Term ctx ty) where
  constructor MkNf
  term : Term ctx ty
  0 steps : t >= term
  0 normal : Normal term

%name NormalForm nf

-- Strong Normalization Proof --------------------------------------------------

invApp : Normal (App t u) -> Neutral (App t u)
invApp (Ntrl n) = n

invRec : Normal (Rec t u v) -> Neutral (Rec t u v)
invRec (Ntrl n) = n

invSuc : Normal (Suc t) -> Normal t
invSuc (Suc n) = n

wknNe : Neutral t -> Neutral (wkn t thin)
wknNf : Normal t -> Normal (wkn t thin)

wknNe Var = Var
wknNe (App n m) = App (wknNe n) (wknNf m)
wknNe (Rec n m k) = Rec (wknNe n) (wknNf m) (wknNf k)

wknNf (Ntrl n) = Ntrl (wknNe n)
wknNf (Abs n) = Abs (wknNf n)
wknNf Zero = Zero
wknNf (Suc n) = Suc (wknNf n)

backStepsNf : NormalForm t -> (0 _ : u >= t) -> NormalForm u
backStepsNf nf steps = MkNf nf.term (steps ++ nf.steps) nf.normal

backStepsRel :
  {ty : Ty} ->
  {0 t, u : Term ctx ty} ->
  LogRel (\t => NormalForm t) t ->
  (0 _ : u >= t) ->
  LogRel (\t => NormalForm t) u
backStepsRel =
  preserve {R = flip (>=)}
    (MkPresHelper (\thin, v, steps => AppCong1' (wknSteps steps)) backStepsNf)

ntrlRel : {ty : Ty} -> {t : Term ctx ty} -> (0 _ : Neutral t) -> LogRel (\t => NormalForm t) t
ntrlRel {ty = N} n = MkNf t [<] (Ntrl n)
ntrlRel {ty = ty ~> ty'} n =
  ( MkNf t [<] (Ntrl n)
  , \thin, u, rel =>
    backStepsRel
      (ntrlRel (App (wknNe n) (escape rel).normal))
      (AppCong2' (escape rel).steps)
  )

recNf' :
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  {u : Term ctx ty} ->
  {v : Term ctx (ty ~> ty)} ->
  (t' : Term ctx N) ->
  (0 n : Normal t') ->
  LogRel (\t => NormalForm t) u ->
  LogRel (\t => NormalForm t) v ->
  LogRel (\t => NormalForm t) (Rec t' u v)
recNf' Zero n relU relV = backStepsRel relU [<RecZero]
recNf' (Suc t') n relU relV =
  let rec = recNf' t' (invSuc n) relU relV in
  let step : Rec (Suc t') u v > App (wkn v id) (Rec t' u v) = rewrite wknId v in RecSuc in
  backStepsRel (snd relV id _ rec) [<step]
recNf' t'@(Var _) n relU relV =
  let nfU = escape relU in
  let nfV = escape {ty = ty ~> ty} relV in
  backStepsRel
    (ntrlRel (Rec Var nfU.normal nfV.normal))
    (RecCong2' nfU.steps ++ RecCong3' nfV.steps)
recNf' t'@(App _ _) n relU relV =
  let nfU = escape relU in
  let nfV = escape {ty = ty ~> ty} relV in
  backStepsRel
    (ntrlRel (Rec (invApp n) nfU.normal nfV.normal))
    (RecCong2' nfU.steps ++ RecCong3' nfV.steps)
recNf' t'@(Rec _ _ _) n relU relV =
  let nfU = escape relU in
  let nfV = escape {ty = ty ~> ty} relV in
  backStepsRel
    (ntrlRel (Rec (invRec n) nfU.normal nfV.normal))
    (RecCong2' nfU.steps ++ RecCong3' nfV.steps)

recNf :
  {ctx : SnocList Ty} ->
  {ty : Ty} ->
  {0 t : Term ctx N} ->
  {u : Term ctx ty} ->
  {v : Term ctx (ty ~> ty)} ->
  NormalForm t ->
  LogRel (\t => NormalForm t) u ->
  LogRel (\t => NormalForm t) v ->
  LogRel (\t => NormalForm t) (Rec t u v)
recNf nf relU relV =
  backStepsRel
    (recNf' nf.term nf.normal relU relV)
    (RecCong1' nf.steps)

helper : ValidHelper (\t => NormalForm t)
helper = MkValidHelper
  { var = \i => ntrlRel Var
  , abs = \rel => let nf = escape rel in MkNf (Abs nf.term) (AbsCong' nf.steps) (Abs nf.normal)
  , zero = MkNf Zero [<] Zero
  , suc = \nf => MkNf (Suc nf.term) (SucCong' nf.steps) (Suc nf.normal)
  , rec = recNf
  , step = \nf, step => backStepsNf nf [<step]
  , wkn = \nf, thin => MkNf (wkn nf.term thin) (wknSteps nf.steps) (wknNf nf.normal)
  }

export
normalize : {ctx : SnocList Ty} -> {ty : Ty} -> (t : Term ctx ty) -> NormalForm t
normalize = allRel helper
