module Encoded.Term

import Data.Vect

import Encoded.Bool
import Encoded.Container
import Encoded.Pair
import Encoded.Sum
import Encoded.Vect

import Term.Syntax

%ambiguity_depth 6
%prefix_record_projections off

-- Utilities ----------------------

rec : Nat -> a -> (a -> a) -> a
rec 0 z s = z
rec (S k) z s = s (rec k z s)

AppVect :
  forall ctx.
  {ty, ty' : Ty} ->
  Term (rec k ty' (ty ~>)) ctx ->
  Vect k (Term ty ctx) ->
  Term ty' ctx
AppVect f [] = f
AppVect f (t :: ts) = AppVect (App f t) ts

-- Definition ------------------------------------------------------------------

TermC : Container
TermC = Cases
  [<(Just N, 0)  -- Var
  , (Nothing, 0) -- Zero
  , (Nothing, 1) -- Suc
  , (Nothing, 3) -- Rec
  , (Nothing, 1) -- Abs
  , (Nothing, 2) -- App
  ]

export
Term : Ty
Term = W TermC

-- Smart Constructors ----------------------------------------------------------

export
Var : Term (N ~> Term) ctx
Var =
  let i = There $ There $ There $ There $ There Here in
  Abs' (\n => App (intro {c = TermC} . tag i) [<App pair [<n, nil]])

export
Zero : Term Term ctx
Zero =
  let i = There $ There $ There $ There Here in
  App (intro {c = TermC} . tag i) [<nil]

export
Suc : Term (Term ~> Term) ctx
Suc =
  let i = There $ There $ There Here in
  Abs' (\t => App (intro {c = TermC} . tag i) [<fromVect [t]])

export
Rec : Term (Term ~> Term ~> Term ~> Term) ctx
Rec =
  let i = There $ There Here in
  AbsAll [<_,_,_] (\[<t, u, v] => App (intro {c = TermC} . tag i) [<fromVect [t, u, v]])

export
Abs : Term (Term ~> Term) ctx
Abs =
  let i = There Here in
  Abs' (\t => App (intro {c = TermC} . tag i) [<fromVect [t]])

export
App : Term (Term ~> Term ~> Term) ctx
App =
  let i = Here in
  AbsAll [<_,_] (\[<t, u] => App (intro {c = TermC} . tag i) [<fromVect [t, u]])

-- Initiality ------------------------------------------------------------------

public export
EliminatorTy : Ty -> Ty
EliminatorTy ty =
  (N ~> ty) *
  (ty) *
  (ty ~> ty) *
  (ty ~> ty ~> ty ~> ty) *
  (ty ~> ty) *
  (ty ~> ty ~> ty)

public export
record Eliminator (ty : Ty) (ctx : SnocList Ty) where
  constructor MkElim
  var : Term (N ~> ty) ctx
  zero : Term ty ctx
  suc : Term (ty ~> ty) ctx
  rec : Term (ty ~> ty ~> ty ~> ty) ctx
  abs : Term (ty ~> ty) ctx
  app : Term (ty ~> ty ~> ty) ctx

%name Eliminator elim

export
unpack : {ty : Ty} -> Term (EliminatorTy ty) ctx -> Eliminator ty ctx
unpack t =
  MkElim
    { var = App (fst . fst . fst . fst . fst) [<t]
    , zero = App (snd . fst . fst . fst . fst) [<t]
    , suc = App (snd . fst . fst . fst) [<t]
    , rec = App (snd . fst . fst) [<t]
    , abs = App (snd . fst) [<t]
    , app = App snd [<t]
    }

export
pack : {ty : Ty} -> Eliminator ty ctx -> Term (EliminatorTy ty) ctx
pack elim =
  App pair
  [<App pair
  [<App pair
  [<App pair
  [<App pair
  [<elim.var
  , elim.zero]
  , elim.suc]
  , elim.rec]
  , elim.abs]
  , elim.app]

export
Elim : {ty : Ty} -> Term (EliminatorTy ty ~> Term ~> ty) ctx
Elim = Abs' (\e =>
  let el = unpack e in
  App (elim {c = TermC})
    [<el.var . fst
    , Const el.zero
    , Abs' (\v => AppVect (shift el.suc) (toVect v))
    , Abs' (\v => AppVect (shift el.rec) (toVect v))
    , Abs' (\v => AppVect (shift el.abs) (toVect v))
    , Abs' (\v => AppVect (shift el.app) (toVect v))
    ])
  where

public export
DiscriminatorTy : Ty -> Ty
DiscriminatorTy ty =
  (N ~> ty) *
  (ty) *
  (Term ~> ty) *
  (Term ~> Term ~> Term ~> ty) *
  (Term ~> ty) *
  (Term ~> Term ~> ty)

public export
record Discriminator (ty : Ty) (ctx : SnocList Ty) where
  constructor MkDiscrim
  var : Term (N ~> ty) ctx
  zero : Term ty ctx
  suc : Term (Term ~> ty) ctx
  rec : Term (Term ~> Term ~> Term ~> ty) ctx
  abs : Term (Term ~> ty) ctx
  app : Term (Term ~> Term ~> ty) ctx

%name Eliminator elim

export
unpackDisc : {ty : Ty} -> Term (DiscriminatorTy ty) ctx -> Discriminator ty ctx
unpackDisc t =
  MkDiscrim
    { var = App (fst . fst . fst . fst . fst) [<t]
    , zero = App (snd . fst . fst . fst . fst) [<t]
    , suc = App (snd . fst . fst . fst) [<t]
    , rec = App (snd . fst . fst) [<t]
    , abs = App (snd . fst) [<t]
    , app = App snd [<t]
    }

export
packDisc : {ty : Ty} -> Discriminator ty ctx -> Term (DiscriminatorTy ty) ctx
packDisc elim =
  App pair
  [<App pair
  [<App pair
  [<App pair
  [<App pair
  [<elim.var
  , elim.zero]
  , elim.suc]
  , elim.rec]
  , elim.abs]
  , elim.app]

export
Inspect : {ty : Ty} -> Term (DiscriminatorTy ty ~> Term ~> ty) ctx
Inspect = Abs' (\e =>
  let el = unpackDisc e in
  App (inspect {c = TermC})
    [<el.var . fst
    , Const el.zero
    , Abs' (\v => AppVect (shift el.suc) (toVect v))
    , Abs' (\v => AppVect (shift el.rec) (toVect v))
    , Abs' (\v => AppVect (shift el.abs) (toVect v))
    , Abs' (\v => AppVect (shift el.app) (toVect v))
    ])

-- Weakening -------------------------------------------------------------------

liftNat : Term ((N ~> N) ~> (N ~> N)) ctx
liftNat = AbsAll [<_,_] (\[<f, n] => App if' [<App isZero [<n], 0, Suc (App f [<n])])

WeakenElim : Eliminator ((N ~> N) ~> Term) ctx
WeakenElim =
  MkElim
    { var = AbsAll [<_,_] (\[<i, f] => App (Var . f) [<i])
    , zero = Const Zero
    , suc = Abs' (\t => Suc . t)
    , rec = AbsAll [<_,_,_,_] (\[<t, u, v, f] => App Rec [<App t [<f], App u [<f], App v [<f]])
    , abs = Abs' (\t => Abs . t . liftNat)
    , app = AbsAll [<_,_,_] (\[<t, u, f] => App App [<App t [<f], App u [<f]])
    }

export
weaken : Term ((N ~> N) ~> Term ~> Term) ctx
weaken = AbsAll [<_,_] (\[<f, t] => App Elim [<pack WeakenElim, t, f])

liftTerm : Term ((N ~> Term) ~> (N ~> Term)) ctx
liftTerm = AbsAll [<_,_] (\[<f, n] =>
  App if'
    [<App isZero [<n]
    , App Var [<0]
    , App weaken [<Op Suc, App f [<n]]])

-- Substitution ----------------------------------------------------------------

SubstElim : Eliminator ((N ~> Term) ~> Term) ctx
SubstElim =
  MkElim
    { var = AbsAll [<_,_] (\[<i, f] => App f [<i])
    , zero = Const Zero
    , suc = Abs' (\t => Suc . t)
    , rec = AbsAll [<_,_,_,_] (\[<t, u, v, f] => App Rec [<App t [<f], App u [<f], App v [<f]])
    , abs = Abs' (\t => Abs . t . liftTerm)
    , app = AbsAll [<_,_,_] (\[<t, u, f] => App App [<App t [<f], App u [<f]])
    }

export
subst : Term ((N ~> Term) ~> Term ~> Term) ctx
subst = AbsAll [<_,_] (\[<f, t] => App Elim [<pack SubstElim, t, f])

-- Reduction -------------------------------------------------------------------

-- Performs an application step.
-- Arguments are whether inspected term stepped, and argument term
AppDisc : Discriminator (Term ~> B ~> Term * B) ctx
AppDisc =
  MkDiscrim
    { var = fallthrough . Var
    , zero = App fallthrough [<Zero]
    , suc = fallthrough . Suc
    , rec = AbsAll [<_,_,_] (\[<t, u, v] => App fallthrough [<App Rec [<t, u, v]])
    , abs = AbsAll [<_,_,_] (\[<t, u, b] =>
      App pair
        [<App subst
          [<Abs' (\n => App if' [<App isZero [<n], shift t, App Var [<pred n]])
          , u
          ]
        , True
        ])
    , app = AbsAll [<_,_] (\[<t, u] => App fallthrough [<App App [<t, u]])
    }
  where
  fallthrough : forall ctx. Term (Term ~> Term ~> B ~> Term * B) ctx
  fallthrough =
    AbsAll [<_,_,_] (\[<t, u, b] =>
      App pair
        [<App App [<t, u]
        , b
        ])

RecDisc : Discriminator (Term ~> Term ~> B ~> Term * B) ctx
RecDisc =
  MkDiscrim
    { var = fallthrough . Var
    , zero = AbsAll [<_,_,_] (\[<u, v, b] =>
      App pair [<u, True])
    , suc = AbsAll [<_,_,_,_] (\[<t, u, v, b] =>
      App pair
        [<App App [<v, App Rec [<t, u, v]]
        , True
        ])
    , rec = AbsAll [<_,_,_] (\[<t, u, v] => App fallthrough [<App Rec [<t, u, v]])
    , abs = fallthrough . Abs
    , app = AbsAll [<_,_] (\[<t, u] => App fallthrough [<App App [<t, u]])
    }
  where
  fallthrough : forall ctx. Term (Term ~> Term ~> Term ~> B ~> Term * B) ctx
  fallthrough =
    AbsAll [<_,_,_,_] (\[<t, u, v, b] =>
      App pair
        [<App Rec [<t, u, v]
        , b
        ])

StepElim : Eliminator (Term * B) ctx
StepElim =
  MkElim
    { var = Abs' (\i => App pair [<App Var [<i], False])
    , zero = App pair [<Term.Zero, False]
    , suc = App mapFst [<Suc]
    , rec = AbsAll [<_,_,_] (\[<t, u, v] =>
      App Inspect
        [<packDisc RecDisc
        , App fst [<t]
        , App fst [<u]
        , App fst [<v]
        , App or [<App snd t, App or [<App snd u, App snd v]]
        ])
    , abs = App mapFst [<Abs]
    , app = AbsAll [<_,_] (\[<t, u] =>
      App Inspect
        [<packDisc AppDisc
        , App fst [<t]
        , App fst [<u]
        , App or [<App snd [<t], App snd [<u]]
        ])
    }

export
reduce : Term (N ~> Term ~> Term) ctx
reduce = Abs' (\n =>
  Rec n
    Id
    (Abs' (\rec =>
      (Abs' {ty = Term * B} (\ub =>
        App if' [<App snd [<ub], App (shift rec) [<App fst [<ub]], App fst [<ub]])) .
      (App Elim [<pack StepElim]))))
