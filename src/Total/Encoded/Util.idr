module Total.Encoded.Util

import public Data.Fin
import public Data.List1
import public Data.List.Elem
import public Data.List.Quantifiers
import public Total.Syntax

%prefix_record_projections off

namespace Bool
  export
  B : Ty
  B = N

  export
  True : Term ctx B
  True = Zero

  export
  False : Term ctx B
  False = Suc Zero

  export
  If : Len ctx => Term ctx B -> Term ctx ty -> Term ctx ty -> Term ctx ty
  If t u v = Rec t u (Abs $ wkn v (Drop id))

namespace Arb
  export
  arb : {ty : Ty} -> Term [<] ty
  arb {ty = N} = Zero
  arb {ty = ty ~> ty'} = Abs (lift arb)

namespace Union
  export
  (<+>) : Ty -> Ty -> Ty
  N <+> N = N
  N <+> (u ~> u') = u ~> u'
  (t ~> t') <+> N = t ~> t'
  (t ~> t') <+> (u ~> u') = (t <+> u) ~> (t' <+> u')

  export
  injL : {t, u : Ty} -> Term [<] (t ~> (t <+> u))
  export
  injR : {t, u : Ty} -> Term [<] (u ~> (t <+> u))
  export
  prjL : {t, u : Ty} -> Term [<] ((t <+> u) ~> t)
  export
  prjR : {t, u : Ty} -> Term [<] ((t <+> u) ~> u)

  injL {t = N, u = N} = Abs' (S Z) id
  injL {t = N, u = u ~> u'} = Abs' (S $ S Z) (\n, _ => App (lift (prjR . injL)) n)
  injL {t = t ~> t', u = N} = Abs' (S Z) id
  injL {t = t ~> t', u = u ~> u'} = Abs' (S Z) (\f => lift injL . f . lift prjL)

  injR {t = N, u = N} = Abs' (S Z) id
  injR {t = N, u = u ~> u'} = Abs' (S Z) id
  injR {t = t ~> t', u = N} = Abs' (S $ S Z) (\n, _ => App (lift (prjL . injR)) n)
  injR {t = t ~> t', u = u ~> u'} = Abs' (S Z) (\f => lift injR . f . lift prjR)

  prjL {t = N, u = N} = Abs' (S Z) id
  prjL {t = N, u = u ~> u'} = Abs' (S Z) (\f => App (lift (prjL . injR) . f) (lift $ arb))
  prjL {t = t ~> t', u = N} = Abs' (S Z) id
  prjL {t = t ~> t', u = u ~> u'} = Abs' (S Z) (\f => lift prjL . f . lift injL)

  prjR {t = N, u = N} = Abs' (S Z) id
  prjR {t = N, u = u ~> u'} = Abs' (S Z) id
  prjR {t = t ~> t', u = N} = Abs' (S Z) (\f => App (lift (prjR . injL) . f) (lift $ arb))
  prjR {t = t ~> t', u = u ~> u'} = Abs' (S Z) (\f => lift prjR . f . lift injR)

namespace Unit
  export
  Unit : Ty
  Unit = N

namespace Pair
  export
  (*) : Ty -> Ty -> Ty
  t * u = B ~> (t <+> u)

  export
  pair : {t, u : Ty} -> Term [<] (t ~> u ~> (t * u))
  pair = Abs' (S $ S $ S Z)
    (\fst, snd, b => If b (App (lift injL) fst) (App (lift injR) snd))

  export
  fst : {t, u : Ty} -> Term [<] ((t * u) ~> t)
  fst = Abs' (S Z) (\p => App (lift prjL . p) True)

  export
  snd : {t, u : Ty} -> Term [<] ((t * u) ~> u)
  snd = Abs' (S Z) (\p => App (lift prjR . p) False)

  export
  mapSnd : {t, u, v : Ty} -> Term [<] ((u ~> v) ~> (t * u) ~> (t * v))
  mapSnd = Abs' (S $ S Z) (\f, p => App' (lift pair) [<App (lift fst) p , App (f . lift snd) p])

  export
  Product : SnocList Ty -> Ty
  Product = foldl (*) Unit

  export
  pair' : {tys : SnocList Ty} -> Term [<] (tys ~>* Product tys)
  pair' {tys = [<]} = arb
  pair' {tys = tys :< ty} = Abs' (S $ S Z) (\p, t => App' (lift pair) [<p, t]) .* pair' {tys}

  export
  project : {tys : SnocList Ty} -> Elem ty tys -> Term [<] (Product tys ~> ty)
  project {tys = tys :< ty} Here = snd
  project {tys = tys :< ty} (There i) = project i . fst

  export
  mapProd :
    {ctx, tys, tys' : SnocList Ty} ->
    {auto 0 prf : SnocList.length tys = SnocList.length tys'} ->
    All (Term ctx) (zipWith (~>) tys tys') ->
    Term ctx (Product tys ~> Product tys')
  mapProd {tys = [<], tys' = [<]} [<] = Abs (Var Here)
  mapProd {tys = tys :< ty, tys' = tys' :< ty', prf} (fs :< f) =
    Abs' (S Z)
      (\p =>
        App' (lift pair)
          [<App (wkn (mapProd fs {prf = injective prf}) (Drop id) . lift fst) p
          , App (wkn f (Drop id) . lift snd) p
          ])

  replicate : Nat -> a -> SnocList a
  replicate 0 x = [<]
  replicate (S n) x = replicate n x :< x

  replicateLen : (n : Nat) -> SnocList.length (replicate n x) = n
  replicateLen 0 = Refl
  replicateLen (S k) = cong S (replicateLen k)

  export
  Vect : Nat -> Ty -> Ty
  Vect n ty = Product (replicate n ty)

  zipReplicate :
    {0 f : a -> b -> c} ->
    {0 p : c -> Type} ->
    {n : Nat} ->
    p (f x y) ->
    SnocList.Quantifiers.All.All p (zipWith f (replicate n x) (replicate n y))
  zipReplicate {n = 0} z = [<]
  zipReplicate {n = S k} z = zipReplicate z :< z

  export
  mapVect :
    {n : Nat} ->
    {ty, ty' : Ty} ->
    Term [<] ((ty ~> ty') ~> Vect n ty ~> Vect n ty')
  mapVect =
    Abs' (S Z)
      (\f => mapProd {prf = trans (replicateLen n) (sym $ replicateLen n)} $ zipReplicate f)

  export
  Nil : {ty : Ty} -> Term [<] (Vect 0 ty)
  Nil = arb

  export
  Cons : {n : Nat} -> {ty : Ty} -> Term [<] (ty ~> Vect n ty ~> Vect (S n) ty)
  Cons = Abs' (S $ S Z) (\t, ts => App' (lift pair) [<ts, t])

  export
  head : {n : Nat} -> {ty : Ty} -> Term [<] (Vect (S n) ty ~> ty)
  head = snd

  export
  tail : {n : Nat} -> {ty : Ty} -> Term [<] (Vect (S n) ty ~> Vect n ty)
  tail = fst

  export
  index : {n : Nat} -> {ty : Ty} -> (i : Fin n) -> Term [<] (Vect n ty ~> ty)
  index FZ = head
  index (FS i) = index i . tail

  export
  enumerate : (n : Nat) -> Term [<] (Vect n N)
  enumerate 0 = arb
  enumerate (S k) = App' pair [<App' mapVect [<Abs' (S Z) Suc, enumerate k], Zero]

namespace Sum
  export
  (+) : Ty -> Ty -> Ty
  t + u = B * (t <+> u)

  export
  left : {t, u : Ty} -> Term [<] (t ~> (t + u))
  left = Abs' (S Z) (\e => App' (lift pair) [<True, App (lift injL) e])

  export
  right : {t, u : Ty} -> Term [<] (u ~> (t + u))
  right = Abs' (S Z) (\e => App' (lift pair) [<False, App (lift injR) e])

  export
  case' : {t, u, ty : Ty} -> Term [<] ((t ~> ty) ~> (u ~> ty) ~> (t + u) ~> ty)
  case' = Abs' (S $ S $ S Z)
    (\f, g, s =>
      If (App (lift fst) s)
        (App (f . lift (prjL . snd)) s)
        (App (g . lift (prjR . snd)) s))

  Sum' : Ty -> List Ty -> Ty
  Sum' ty [] = ty
  Sum' ty (ty' :: tys) = ty + Sum' ty' tys

  export
  Sum : List1 Ty -> Ty
  Sum (ty ::: tys) = Sum' ty tys

  put' :
    {ty, ty' : Ty} ->
    {tys : List Ty} ->
    (i : Elem ty (ty' :: tys)) ->
    Term [<] (ty ~> Sum' ty' tys)
  put' {tys = []} Here = Abs' (S Z) id
  put' {tys = _ :: _} Here = left
  put' {tys = _ :: _} (There i) = right . put' i

  export
  put : {tys : List1 Ty} -> {ty : Ty} -> (i : Elem ty (forget tys)) -> Term [<] (ty ~> Sum tys)
  put {tys = _ ::: _} i = put' i

  caseAll' :
    {ctx : SnocList Ty} ->
    {ty, ty' : Ty} ->
    {tys : List Ty} ->
    All (Term ctx . (~> ty)) (ty' :: tys) ->
    Term ctx (Sum' ty' tys ~> ty)
  caseAll' (t :: []) = t
  caseAll' (t :: u :: ts) = App' (lift case') [<t, caseAll' (u :: ts)]

  export
  caseAll :
    {ctx : SnocList Ty} ->
    {tys : List1 Ty} ->
    {ty : Ty} ->
    All (Term ctx . (~> ty)) (forget tys) ->
    Term ctx (Sum tys ~> ty)
  caseAll {tys = _ ::: _} = caseAll'

namespace Nat
  export
  IsZero : Term [<] (N ~> B)
  IsZero = Abs' (S Z) (\m => Rec m (lift True) (Abs (lift False)))

  export
  Add : Term [<] (N ~> N ~> N)
  Add = Abs' (S $ S Z) (\m, n => Rec m n (Abs' (S Z) Suc))

  export
  sum : {n : Nat} -> Term [<] (Vect n N ~> N)
  sum {n = 0} = Abs Zero
  sum {n = S k} = Abs' (S Z)
    (\ns => App' (lift Add) [<App (lift head) ns, App (lift (sum . tail)) ns])

  export
  Pred : Term [<] (N ~> N)
  Pred = Abs' (S Z)
    (\m =>
      App' (lift case')
        [<Abs Zero
        , Abs' (S Z) id
        , Rec m
            (lift $ App left (arb {ty = Unit}))
            (App' (lift case')
              [<Abs (lift $ App right Zero)
              , Abs' (S Z) (\n => App (lift right) (Suc n))
              ])
        ])

  export
  Sub : Term [<] (N ~> N ~> N)
  Sub = Abs' (S $ S Z) (\m, n => Rec n m (lift Pred))

  export
  LE : Term [<] (N ~> N ~> B)
  LE = Abs' (S Z) (\m => lift IsZero . App (lift Sub) m)

  export
  LT : Term [<] (N ~> N ~> B)
  LT = Abs' (S Z) (\m => App (lift LE) (Suc m))

  export
  Cond :
    {ctx : SnocList Ty} ->
    {ty : Ty} ->
    List (Term ctx N, Term ctx (N ~> ty)) ->
    Term ctx (N ~> ty)
  Cond [] = lift arb
  Cond ((n, v) :: xs) =
    Abs' (S Z)
      (\t =>
        If (App' (lift LE) [<t, wkn n (Drop id)])
          (App (wkn v (Drop id)) t)
          (App (wkn (Cond xs) (Drop id)) (App' (lift Sub) [<t, wkn n (Drop id)])))

namespace Data
  public export
  Shape : Type
  Shape = (Ty, Nat)

  public export
  Container : Type
  Container = List1 Shape

  public export
  fillShape : Shape -> Ty -> Ty
  fillShape (shape,  n) ty = shape * Vect n ty

  public export
  fill : Container -> Ty -> Ty
  fill c ty = Sum (map (flip fillShape ty) c)

  export
  fix : Container -> Ty
  fix c = Product [<N, N ~> N, N ~> fill c N]
  --                ^  ^       ^- tags and next positions
  --                |  |- offset
  --                |- pred (number of tags in structure)

  mapShape :
    {shape : Shape} ->
    {ty, ty' : Ty} ->
    Term [<] ((ty ~> ty') ~> fillShape shape ty ~> fillShape shape ty')
  mapShape {shape = (shape, n)} = mapSnd . mapVect

  gmap :
    {0 f : a -> b} ->
    {0 P : a -> Type} ->
    {0 Q : b -> Type} ->
    ({x : a} -> P x -> Q (f x)) ->
    {xs : List a} ->
    All P xs ->
    All Q (map f xs)
  gmap f [] = []
  gmap f (px :: pxs) = f px :: gmap f pxs

  forgetMap :
    (0 f : a -> b) ->
    (0 xs : List1 a) ->
    forget (map f xs) = map f (forget xs)
  forgetMap f (head ::: tail) = Refl

  calcOffsets :
    {ctx : SnocList Ty} ->
    {c : Container} ->
    {n : Nat} ->
    (ts : Term ctx (Vect n (fix c))) ->
    (acc : Term ctx N) ->
    List (Term ctx N, Term ctx (N ~> N))
  calcOffsets {n = 0} ts acc = []
  calcOffsets {n = S k} ts acc =
    let hd = App (lift head) ts in
    let n = App (lift $ project $ There $ There Here) hd in
    let offset = App (lift $ project $ There Here) hd in
    (n, App (lift Add) acc . offset) ::
    calcOffsets
      (App (lift tail) ts)
      (App' (lift Add) [<Suc n, acc])

  calcData :
    {ctx : SnocList Ty} ->
    {c : Container} ->
    {n : Nat} ->
    (ts : Term ctx (Vect n (fix c))) ->
    (acc : Term ctx N) ->
    List (Term ctx N, Term ctx (N ~> fill c N))
  calcData {n = 0} ts acc = []
  calcData {n = S k} ts acc =
    let hd = App (lift head) ts in
    let n = App (lift $ project $ There $ There Here) hd in
    (n, App (lift $ project Here) hd) ::
    calcData
      (App (lift tail) ts)
      (App' (lift Add) [<Suc n, acc])

  export
  intro :
    {c : Container} ->
    {shape : Shape} ->
    Elem shape (forget c) ->
    Term [<] (fillShape shape (fix c) ~> fix c)
  intro {shape = (shape, n)} i = Abs' (S Z)
    (\t =>
      App' (lift $ pair' {tys = [<N, N ~> N, N ~> fill c N]})
        [<App (lift (sum . App mapVect (Abs' (S Z) Suc . project (There $ There Here)) . snd)) t
        , Cond ((Zero, Abs' (S Z) Suc) :: calcOffsets (App (lift snd) t) (Suc Zero))
        , Cond
          (  (Zero,
              Abs
                (App
                  (lift $ put {tys = map (flip fillShape N) c} $
                    rewrite forgetMap (flip fillShape N) c in
                    elemMap (flip fillShape N) i)
                  (App' (lift mapSnd) [<Abs (lift $ enumerate n), wkn t (Drop id)])))
          :: calcData (App (lift snd) t) (Suc Zero)
          )
        ])

  export
  elim :
    {c : Container} ->
    {ctx : SnocList Ty} ->
    {ty : Ty} ->
    All (Term ctx . (~> ty) . flip Data.fillShape ty) (forget c) ->
    Term ctx (fix c ~> ty)
  elim cases = Abs' (S Z)
    (\t =>
      let tags = Suc (App (lift $ project $ There $ There Here) t) in
      let offset = App (lift $ project $ There Here) (wkn t (Drop $ Drop id)) in
      let vals = App (lift $ project $ Here) (wkn t (Drop $ Drop id)) in
      App'
        (Rec tags
          (lift arb)
          (Abs' (S $ S Z) (\rec, n =>
            App
              (caseAll {tys = map (flip fillShape N) c}
                (rewrite forgetMap (flip fillShape N) c in
                 gmap
                   (\f =>
                     wkn f (Drop $ Drop $ Drop id) .
                     App (lift mapShape) (rec . App (lift Add) (App offset n)))
                   cases) .
               vals)
              n)))
        [<Zero])

  -- elim cases (#tags-1,offset,data) =
  --   let
  --       step : (N -> ty) -> (N -> ty)
  --       step rec n =
  --         case rec n of
  --           i => cases(i) . mapShape (rec . (+ offset n))
  --   in
  --       rec #tags arb step 0
