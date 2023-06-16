module Term.Semantics

import Term
import public Data.SnocList.Quantifiers

public export
TypeOf : Ty -> Type
TypeOf N = Nat
TypeOf (ty ~> ty') = TypeOf ty -> TypeOf ty'

rec : Nat -> a -> (a -> a) -> a
rec 0 x f = x
rec (S k) x f = f (rec k x f)

fullSem : FullTerm ty ctx -> ctx `Thins` ctx' -> All TypeOf ctx' -> TypeOf ty
fullSem Var thin ctx = indexAll (index thin Here) ctx
fullSem (Const t) thin ctx = const (fullSem t thin ctx)
fullSem (Abs t) thin ctx = \v => fullSem t (Keep thin) (ctx :< v)
fullSem (App (MakePair (t `Over` thin1) (u `Over` thin2) _)) thin ctx =
  fullSem t (thin . thin1) ctx (fullSem u (thin . thin2) ctx)
fullSem Zero thin ctx = 0
fullSem (Suc t) thin ctx = S (fullSem t thin ctx)
fullSem
  (Rec (MakePair
    (t `Over` thin1)
    (MakePair (u `Over` thin2) (v `Over` thin3) _ `Over` thin')
    _))
  thin
  ctx =
  let thin' = thin . thin' in
  rec
    (fullSem t (thin . thin1) ctx)
    (fullSem u (thin' . thin2) ctx)
    (fullSem v (thin' . thin3) ctx)

export
sem : Term ty ctx -> All TypeOf ctx -> TypeOf ty
sem (t `Over` thin) ctx = fullSem t thin ctx
