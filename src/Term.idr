module Term

import Control.Order
import Control.Relation
import Data.Fin
import Data.Fin.Extra
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic

import public Data.SnocList.Quantifiers
import public Thinned
import public Type

%prefix_record_projections off

-- Definition ------------------------------------------------------------------

public export
data Operator : List Ty -> Ty -> Type where
  Lit : (n : Nat) -> Operator [] N
  Suc : Operator [N] N
  Plus : Operator [N, N] N
  Mult : Operator [N, N] N
  Pred : Operator [N] N
  Minus : Operator [N, N] N
  Div : Operator [N, N] N
  Mod : Operator [N, N] N

%name Operator op

||| System T terms that use all the variables in scope.
public export
data FullTerm : Ty -> SnocList Ty -> Type where
  Var : FullTerm ty [<ty]
  Const : FullTerm ty' ctx -> FullTerm (ty ~> ty') ctx
  Abs : FullTerm ty' (ctx :< ty) -> FullTerm (ty ~> ty') ctx
  App :
    {ty : Ty} ->
    Pair (FullTerm (ty ~> ty')) (FullTerm ty) ctx ->
    FullTerm ty' ctx
  Op : Operator tys ty -> FullTerm (foldr (~>) ty tys) [<]
  Rec :
    {ty : Ty} ->
    Pair (FullTerm N) (Pair (FullTerm ty) (FullTerm (ty ~> ty))) ctx ->
    FullTerm ty ctx

%name FullTerm t, u, v

||| System T terms.
public export
Term : Ty -> SnocList Ty -> Type
Term ty ctx = Thinned (FullTerm ty) ctx

-- Smart Constructors ----------------------------------------------------------

namespace Smart
  export
  Var : Elem ty ctx -> Term ty ctx
  Var i = Var `Over` Point i

  export
  Const : Term ty' ctx -> Term (ty ~> ty') ctx
  Const t = map Const t

  export
  Abs : Term ty' (ctx :< ty) -> Term (ty ~> ty') ctx
  Abs (t `Over` Empty) = Const t `Over` Empty
  Abs (t `Over` Drop thin) = Const t `Over` thin
  -- Prevent eta expansion
  Abs (App (MakePair (t `Over` Drop thin1) (Var `Over` Keep _) _) `Over` Id) = t `Over` thin1
  Abs (App (MakePair (t `Over` Drop thin1) (Var `Over` Id) _) `Over` Id) = t `Over` thin1
  Abs (App (MakePair (t `Over` Empty) (Var `Over` Keep _) _) `Over` Id) = t `Over` Empty
  Abs (App (MakePair (t `Over` Empty) (Var `Over` Id) _) `Over` Id) = t `Over` Empty
  Abs (App (MakePair (t `Over` Drop thin1) (Var `Over` Keep _) _) `Over` Keep thin) = t `Over` thin . thin1
  Abs (App (MakePair (t `Over` Drop thin1) (Var `Over` Id) _) `Over` Keep thin) = t `Over` thin . thin1
  Abs (App (MakePair (t `Over` Empty) (Var `Over` Keep _) _) `Over` Keep thin) = t `Over` Empty
  Abs (App (MakePair (t `Over` Empty) (Var `Over` Id) _) `Over` Keep thin) = t `Over` Empty
  -- Otherwise abstract as normal
  Abs (t `Over` Id) = Abs t `Over` Id
  Abs (t `Over` Keep thin) = Abs t `Over` thin

  export
  App : {ty : Ty} -> Term (ty ~> ty') ctx -> Term ty ctx -> Term ty' ctx
  App t u = map App $ MkPair t u

  export
  Op : Operator tys ty -> Term (foldr (~>) ty tys) ctx
  Op op = Op op `Over` Empty

  export
  Rec' : {ty : Ty} -> Term N ctx -> Term ty ctx -> Term (ty ~> ty) ctx -> Term ty ctx
  Rec' t u v = map Rec $ MkPair t (MkPair u v)

  --- Properties

  export
  varCong : {0 i, j : Elem ty ctx} -> i = j -> Var i <~> Var j
  varCong Refl = irrelevantEquiv reflexive

  export
  shiftVar : (i : Elem ty ctx) -> shift (Var i) <~> Var (There i)
  shiftVar i = UpToThin (dropPoint i)

  export
  constCong : {0 t, u : Term ty' ctx} -> t <~> u -> Const t <~> Const u
  constCong prf = mapCong Const prf

  export
  absCong : {0 t, u : Term ty' (ctx :< ty)} -> t <~> u -> Abs t <~> Abs u

  export
  appCong :
    {0 t1, u1 : Term (ty ~> ty') ctx} ->
    {0 t2, u2 : Term ty ctx} ->
    t1 <~> u1 ->
    t2 <~> u2 ->
    App t1 t2 <~> App u1 u2

  export
  recCong :
    {0 t1, u1 : Term N ctx} ->
    {0 t2, u2 : Term ty ctx} ->
    {0 t3, u3 : Term (ty ~> ty) ctx} ->
    t1 <~> u1 ->
    t2 <~> u2 ->
    t3 <~> u3 ->
    Rec' t1 t2 t3 <~> Rec' u1 u2 u3

-- Substitution Definition -----------------------------------------------------

||| Substitution of variables for terms.
public export
data Subst : (ctx, ctx' : SnocList Ty) -> Type where
  Base : ctx `Thins` ctx' -> Subst ctx ctx'
  (:<) : Subst ctx ctx' -> Term ty ctx' -> Subst (ctx :< ty) ctx'

%name Subst sub

export
index : Subst ctx ctx' -> Elem ty ctx -> Term ty ctx'
index (Base thin) i = Var (index thin i)
index (sub :< v) Here = v
index (sub :< v) (There i) = index sub i

||| Equivalence relation on substitutions.
public export
record (<~>) (sub1, sub2 : Subst ctx ctx') where
  constructor MkEquivalence
  equiv : forall ty. (i : Elem ty ctx) -> index sub1 i <~> index sub2 i

%name Term.(<~>) prf

--- Properties

export
irrelevantEquiv :
  {0 sub1, sub2 : Subst ctx ctx'} ->
  (0 prf : sub1 <~> sub2) ->
  sub1 <~> sub2
irrelevantEquiv prf = MkEquivalence (\i => irrelevantEquiv $ prf.equiv i)

export
Reflexive (Subst ctx ctx') (<~>) where
  reflexive = MkEquivalence (\i => reflexive)

export
Symmetric (Subst ctx ctx') (<~>) where
  symmetric prf = MkEquivalence (\i => symmetric $ prf.equiv i)

export
Transitive (Subst ctx ctx') (<~>) where
  transitive prf1 prf2 = MkEquivalence (\i => transitive (prf1.equiv i) (prf2.equiv i))

export
Equivalence (Subst ctx ctx') (<~>) where

export
Preorder (Subst ctx ctx') (<~>) where

namespace Subst
  export
  Base :
    {0 thin1, thin2 : ctx `Thins` ctx'} ->
    thin1 <~> thin2 ->
    Base thin1 <~> Base thin2
  Base prf = MkEquivalence (\i => varCong (prf.equiv i))

  export
  (:<) :
    {0 sub1, sub2 : Subst ctx ctx'} ->
    {0 t, u : Term ty ctx'} ->
    sub1 <~> sub2 ->
    t <~> u ->
    sub1 :< t <~> sub2 :< u
  prf1 :< prf2 =
    MkEquivalence (\i => case i of Here => prf2; There i => prf1.equiv i)

-- Operations ------------------------------------------------------------------

||| Shifts a substitution under a binder.
export
shift : Subst ctx ctx' -> Subst ctx (ctx' :< ty)
shift (Base thin) = Base (Drop thin)
shift (sub :< t) = shift sub :< shift t

||| Lifts a substitution under a binder.
export
lift : Subst ctx ctx' -> Subst (ctx :< ty) (ctx' :< ty)
lift sub = shift sub :< Var Here

||| Limits the domain of a substitution
export
(.) : Subst ctx' ctx'' -> ctx `Thins` ctx' -> Subst ctx ctx''
Base thin' . thin = Base (thin' . thin)
(sub :< t) . Id = sub :< t
(sub :< t) . Empty = Base Empty
(sub :< t) . Drop thin = sub . thin
(sub :< t) . Keep thin = sub . thin :< t

--- Properties

export
shiftIndex :
  (sub : Subst ctx ctx') ->
  (i : Elem ty ctx) ->
   shift (index sub i) <~> index (shift sub) i
shiftIndex (Base thin) i = CalcWith $
  |~ shift (Var $ index thin i)
  <~ Var (There $ index thin i) ...(shiftVar (index thin i))
  <~ Var (index (Drop thin) i)  ..<(varCong $ indexDrop thin i)
shiftIndex (sub :< v) Here = reflexive
shiftIndex (sub :< v) (There i) = shiftIndex sub i

export
shiftCong : {0 sub1, sub2 : Subst ctx' ctx''} -> sub1 <~> sub2 -> shift sub1 <~> shift sub2
shiftCong prf = irrelevantEquiv $ MkEquivalence (\i =>
  CalcWith $
    |~ index (shift sub1) i
    <~ shift (index sub1 i) ..<(shiftIndex sub1 i)
    <~ shift (index sub2 i) ...(shiftCong (prf.equiv i))
    <~ index (shift sub2) i ...(shiftIndex sub2 i))

export
liftCong : {0 sub1, sub2 : Subst ctx' ctx''} -> sub1 <~> sub2 -> lift sub1 <~> lift sub2
liftCong prf = shiftCong prf :< (irrelevantEquiv $ reflexive)

export
indexHomo :
  (sub : Subst ctx' ctx'') ->
  (thin : ctx `Thins` ctx') ->
  (i : Elem ty ctx) ->
  index sub (index thin i) = index (sub . thin) i
indexHomo (Base thin') thin i = cong Var (indexHomo thin' thin i)
indexHomo (sub :< v) Id i = cong (index (sub :< v)) $ indexId i
indexHomo (sub :< v) (Drop thin) i = Calc $
  |~ index (sub :< v) (index (Drop thin) i)
  ~~ index (sub :< v) (There (index thin i)) ...(cong (index (sub :< v)) $ indexDrop thin i)
  ~~ index sub (index thin i)                ...(Refl)
  ~~ index (sub . thin) i                    ...(indexHomo sub thin i)
indexHomo (sub :< v) (Keep thin) Here = Calc $
  |~ index (sub :< v) (index (Keep thin) Here)
  ~~ index (sub :< v) Here                     ...(cong (index (sub :< v)) $ indexKeepHere thin)
  ~~ v                                         ...(Refl)
indexHomo (sub :< v) (Keep thin) (There i) = Calc $
  |~ index (sub :< v) (index (Keep thin) (There i))
  ~~ index (sub :< v) (There (index thin i))       ...(cong (index (sub :< v)) $ indexKeepThere thin i)
  ~~ index sub (index thin i)                      ...(Refl)
  ~~ index (sub . thin) i                          ...(indexHomo sub thin i)

export
compCong :
  {0 sub1, sub2 : Subst ctx' ctx''} ->
  {0 thin1, thin2 : ctx `Thins` ctx'} ->
  sub1 <~> sub2 ->
  thin1 <~> thin2 ->
  (sub1 . thin1) <~> (sub2 . thin2)
compCong prf1 prf2 = irrelevantEquiv $ MkEquivalence (\i => CalcWith $
  |~ index (sub1 . thin1) i
  ~~ index sub1 (index thin1 i) ..<(indexHomo sub1 thin1 i)
  <~ index sub2 (index thin1 i) ...(prf1.equiv (index thin1 i))
  ~~ index sub2 (index thin2 i) ...(cong (index sub2) $ prf2.equiv i)
  ~~ index (sub2 . thin2) i     ...(indexHomo sub2 thin2 i))

-- Utilities -------------------------------------------------------------------

||| Returns `Just k` if `v` occurs less than `n` times in `v`, else `Nothing`
export
usedLessThan : (n : Nat) -> (t : Term ty ctx) -> (v : Elem ty' ctx) -> Maybe (Fin n)
fullUsedLessThan : (n : Nat) -> FullTerm ty ctx -> Elem ty' ctx -> Maybe (Fin n)

usedLessThan 0 (t `Over` thin) i = Nothing
usedLessThan (S n) (t `Over` thin) i with (preimage thin i)
  _ | Just j = fullUsedLessThan (S n) t j
  _ | Nothing = Just FZ

addFin : (k : Fin n) -> (x : Fin (n `minus` finToNat k)) -> Fin n
addFin k x = natToFinLT (finToNat k + finToNat x) @{prf k x}
  where
  prf :
    forall n. (k : Fin n) -> (x : Fin (n `minus` finToNat k)) ->
    finToNat k + finToNat x `LT` n
  prf FZ x = elemSmallerThanBound x
  prf (FS k) x = LTESucc (prf k x)

-- Used at least once, so needs a Fin 2 or more
fullUsedLessThan 0 t i = Nothing
fullUsedLessThan 1 t i = Nothing
  -- See!
fullUsedLessThan (S (S n)) Var Here = Just (FS FZ)
fullUsedLessThan n (Const t) i = fullUsedLessThan n t i
fullUsedLessThan n (Abs t) i = fullUsedLessThan n t (There i)
fullUsedLessThan n (App (MakePair t u _)) i = do
  k <- usedLessThan n t i
  l <- usedLessThan (n `minus` finToNat k) u i
  Just (addFin k l)
fullUsedLessThan
  n
  (Rec (MakePair
    t
    (MakePair (u `Over` thin1) (v `Over` thin2) _ `Over` thin)
    _))
  i = do
  k1 <- usedLessThan n t i

  let Just i = preimage thin i
    | Nothing => Just k1

  case (preimage thin1 i, preimage thin2 i) of
    (Just i1, Just i2) => do
      k2 <- fullUsedLessThan (n `minus` finToNat k1) u i1
      k3 <- fullUsedLessThan ((n `minus` finToNat k1) `minus` finToNat k2) v i2
      Just (addFin k1 (addFin k2 k3))
    (Just i1, Nothing) => do
      k2 <- fullUsedLessThan (n `minus` finToNat k1) u i1
      Just (addFin k1 k2)
    (Nothing, Just i2) => do
      k2 <- fullUsedLessThan (n `minus` finToNat k1) v i2
      Just (addFin k1 k2)
    (Nothing, Nothing) => Just k1

export
smallerThan : Nat -> Term ty ctx -> Maybe Nat
fullSmallerThan : Nat -> FullTerm ty ctx -> Maybe Nat

smallerThan limit (t `Over` thin) = fullSmallerThan limit t

fullSmallerThan Z _ = Nothing
fullSmallerThan (S limit) Var = Just limit
fullSmallerThan (S limit) (Const t) = fullSmallerThan limit t
fullSmallerThan (S limit) (Abs t) = fullSmallerThan limit t
fullSmallerThan (S limit) (App (MakePair t u _)) = do
  limit <- smallerThan limit t
  smallerThan limit u
fullSmallerThan (S limit) (Op op) = Just limit
fullSmallerThan (S limit) (Rec (MakePair t (MakePair u v _ `Over` _) _)) = do
  limit <- smallerThan limit t
  limit <- smallerThan limit u
  smallerThan limit v

export
countUses : Term ty ctx -> Elem ty' ctx -> Nat
fullCountUses : FullTerm ty ctx -> Elem ty' ctx -> Nat

countUses (t `Over` thin) i =
  case preimage thin i of
    Just i => fullCountUses t i
    Nothing => 0

fullCountUses Var Here = 1
fullCountUses (Const t) i = fullCountUses t i
fullCountUses (Abs t) i = fullCountUses t (There i)
fullCountUses (App (MakePair t u _)) i = countUses t i + countUses u i
fullCountUses
  (Rec (MakePair
    t
    (MakePair (u `Over` thin2) (v `Over` thin3) _ `Over` thin)
    _))
  i =
  countUses t i +
  case preimage thin i of
    Just i =>
      (case preimage thin2 i of Just i => fullCountUses u i; Nothing => 0) +
      (case preimage thin3 i of Just i => fullCountUses v i; Nothing => 0)
    Nothing => 0

export
size : Term ty ctx -> Nat
fullSize : FullTerm ty ctx -> Nat

size (t `Over` thin) = fullSize t

fullSize Var = 1
fullSize (Const t) = S (fullSize t)
fullSize (Abs t) = S (fullSize t)
fullSize (App (MakePair t u _)) = S (size t + size u)
fullSize (Op op) = 1
fullSize (Rec (MakePair t (MakePair u v _ `Over` _) _)) = S (size t + size u + size v)

export
shouldExpand : FullTerm ty (ctx :< ty') -> Term ty' ctx' -> Bool
shouldExpand t u = isJust (smallerThan 1 u) || isJust (fullUsedLessThan 2 t Here)

export
shouldRec : Nat -> Term (ty ~> ty') ctx -> Bool
shouldRec n t = isJust $ smallerThan (3 `max` (10 `div` n)) t

-- Substitution Operation ------------------------------------------------------

export
app : {ty : Ty} -> Term (ty ~> ty') ctx -> Lazy (Term ty ctx) -> Term ty' ctx
export
rec : {ty : Ty} -> {default 0 reps : Nat} -> Term N ctx -> Lazy (Term ty ctx) -> Lazy (Term (ty ~> ty) ctx) -> Term ty ctx
||| Applies a substitution to a term.
export
subst : Term ty ctx -> Subst ctx ctx' -> Term ty ctx'
fullSubst : FullTerm ty ctx -> Subst ctx ctx' -> Term ty ctx'

app (Const t `Over` thin) u = t `Over` thin
app (Abs t `Over` thin) u =
  if shouldExpand t u
  then
    subst (t `Over` Keep thin) (Base Id :< u)
  else
    App (Abs t `Over` thin) u
app t u = App t u

%inline
isConst : Term (ty ~> ty') ctx -> Maybe (Term ty' ctx)
isConst (Const t `Over` thin) = Just (t `Over` thin)
isConst _ = Nothing

doRec : Nat -> (Lazy a -> a) -> Lazy a -> a
doRec 0 f x = x
doRec (S k) f x = doRec k f (f x)

rec (Op (Lit 0) `Over` thin) u v = u
rec (Op (Lit (S k)) `Over` thin) u v =
  case isConst v of
    Just v => v
    Nothing =>
      if shouldRec (S k + reps) v
      then
        doRec (S k) (app v) u
      else
        Rec' (Op (Lit (S k)) `Over` Empty) u v
rec (App (MakePair (Op Suc `Over` _) t _) `Over` thin) u v =
  app v (rec {reps = S reps} (assert_smaller t $ wkn t thin) u v)
rec t u v = Rec' t u v

subst (t `Over` thin) sub = fullSubst t (sub . thin)

fullSubst Var sub = index sub Here
fullSubst (Const t) sub = Const (fullSubst t sub)
fullSubst (Abs t) sub = Abs (fullSubst t $ lift sub)
fullSubst (App (MakePair (t `Over` thin1) (u `Over` thin2) _)) sub =
  assert_total $
  app (fullSubst t $ sub . thin1) (fullSubst u $ sub . thin2)
fullSubst (Op op) sub = Op op
fullSubst
  (Rec (MakePair
    (t `Over` thin1)
    (MakePair (u `Over` thin2) (v `Over` thin3) _ `Over` thin')
    _))
  sub =
  assert_total $
  rec
    (fullSubst t $ sub . thin1)
    (fullSubst u $ sub . thin' . thin2)
    (fullSubst v $ sub . thin' . thin3)

--- Properties

fullSubstCong :
  (t : FullTerm ty ctx) ->
  {0 sub1, sub2 : Subst ctx ctx'} ->
  sub1 <~> sub2 ->
  fullSubst t sub1 <~> fullSubst t sub2

export
substCong :
  {0 t, u : Term ty ctx} ->
  {0 sub1, sub2 : Subst ctx ctx'} ->
  t <~> u ->
  sub1 <~> sub2 ->
  subst t sub1 <~> subst u sub2
substCong (UpToThin prf1) prf2 = irrelevantEquiv $ fullSubstCong _ (compCong prf2 prf1)

export
substBase :
  (t : Term ty ctx) ->
  (thin : ctx `Thins` ctx') ->
  subst t (Base thin) <~> wkn t thin
