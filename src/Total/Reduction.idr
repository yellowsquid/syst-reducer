module Total.Reduction

import Syntax.PreorderReasoning
import Total.Term

public export
data (>) : Term ctx ty -> Term ctx ty -> Type where
  AbsCong : t > u -> Abs t > Abs u
  AppCong1 : t > u -> App t v > App u v
  AppCong2 : u > v -> App t u > App t v
  AppBeta : App (Abs t) u > subst t (Base Id :< u)
  SucCong : t > u -> Suc t > Suc u
  RecCong1 : t1 > t2 -> Rec t1 u v > Rec t2 u v
  RecCong2 : u1 > u2 -> Rec t u1 v > Rec t u2 v
  RecCong3 : v1 > v2 -> Rec t u v1 > Rec t u v2
  RecZero : Rec Zero u v > u
  RecSuc : Rec (Suc t) u v > App v (Rec t u v)

%name Reduction.(>) step

public export
data (>=) : Term ctx ty -> Term ctx ty -> Type where
  Lin : t >= t
  (:<) : t >= u -> u > v -> t >= v

%name Reduction.(>=) steps

export
(++) : t >= u -> u >= v -> t >= v
steps ++ [<] = steps
steps ++ steps' :< step = (steps ++ steps') :< step

export
AbsCong' : t >= u -> Abs t >= Abs u
AbsCong' [<] = [<]
AbsCong' (steps :< step) = AbsCong' steps :< AbsCong step

export
AppCong1' : t >= u -> App t v >= App u v
AppCong1' [<] = [<]
AppCong1' (steps :< step) = AppCong1' steps :< AppCong1 step

export
AppCong2' : u >= v -> App t u >= App t v
AppCong2' [<] = [<]
AppCong2' (steps :< step) = AppCong2' steps :< AppCong2 step

export
SucCong' : t >= u -> Suc t >= Suc u
SucCong' [<] = [<]
SucCong' (steps :< step) = SucCong' steps :< SucCong step

export
RecCong1' : t1 >= t2 -> Rec t1 u v >= Rec t2 u v
RecCong1' [<] = [<]
RecCong1' (steps :< step) = RecCong1' steps :< RecCong1 step

export
RecCong2' : u1 >= u2 -> Rec t u1 v >= Rec t u2 v
RecCong2' [<] = [<]
RecCong2' (steps :< step) = RecCong2' steps :< RecCong2 step

export
RecCong3' : v1 >= v2 -> Rec t u v1 >= Rec t u v2
RecCong3' [<] = [<]
RecCong3' (steps :< step) = RecCong3' steps :< RecCong3 step

-- Properties ------------------------------------------------------------------

lemma :
  (t : Term (ctx :< ty) ty') ->
  (thin : ctx `Thins` ctx') ->
  (u : Term ctx ty) ->
  subst (wkn t (keep thin)) (Base Id :< wkn u thin) = wkn (subst t (Base Id :< u)) thin
lemma t thin u = Calc $
  |~ subst (wkn t (keep thin)) (Base Id :< wkn u thin)
  ~~ subst t (restrict (Base Id :< wkn u thin) (keep thin))
    ...(substWkn t (keep thin) (Base Id :< wkn u thin))
  ~~ subst t (Base thin :< wkn u thin)
    ...(cong (subst t) $ restrictKeep (Base Id) (wkn u thin) thin)
  ~~ subst t (Base (thin . Id) :< wkn u thin)
    ...(sym $ cong (subst t . (:< wkn u thin) . Base) $ identityRight thin)
  ~~ wkn (subst t (Base Id :< u)) thin
    ...(sym $ wknSubst t (Base Id :< u) thin)

export
wknStep : t > u -> wkn t thin > wkn u thin
wknStep (AbsCong step) = AbsCong (wknStep step)
wknStep (AppCong1 step) = AppCong1 (wknStep step)
wknStep (AppCong2 step) = AppCong2 (wknStep step)
wknStep (AppBeta {t, u}) {thin} = rewrite sym $ lemma t thin u in AppBeta
wknStep (SucCong step) = SucCong (wknStep step)
wknStep (RecCong1 step) = RecCong1 (wknStep step)
wknStep (RecCong2 step) = RecCong2 (wknStep step)
wknStep (RecCong3 step) = RecCong3 (wknStep step)
wknStep RecZero = RecZero
wknStep RecSuc = RecSuc

export
wknSteps : t >= u -> wkn t thin >= wkn u thin
wknSteps [<] = [<]
wknSteps (steps :< step) = wknSteps steps :< wknStep step
