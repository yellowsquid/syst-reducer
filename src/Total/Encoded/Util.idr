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
  true : FullTerm B [<]
  true = zero

  export
  false : FullTerm B [<]
  false = suc zero

  export
  if' : FullTerm (B ~> ty ~> ty ~> ty) [<]
  if' = abs' (S $ S $ S Z) (\b, t, f => rec b t (abs $ drop f))

namespace Arb
  export
  arb : {ty : Ty} -> FullTerm ty [<]
  arb {ty = N} = zero
  arb {ty = ty ~> ty'} = abs (lift arb)

namespace Union
  export
  (<+>) : Ty -> Ty -> Ty
  N <+> N = N
  N <+> (u ~> u') = u ~> u'
  (t ~> t') <+> N = t ~> t'
  (t ~> t') <+> (u ~> u') = (t <+> u) ~> (t' <+> u')

  export
  swap : {t, u : Ty} -> FullTerm ((t <+> u) ~> (u <+> t)) [<]
  swap {t = N, u = N} = id
  swap {t = N, u = u ~> u'} = id
  swap {t = t ~> t', u = N} = id
  swap {t = t ~> t', u = u ~> u'} = abs' (S Z) (\f => drop swap . f . drop swap)

  export
  injL : {t, u : Ty} -> FullTerm (t ~> (t <+> u)) [<]
  export
  injR : {t, u : Ty} -> FullTerm (u ~> (t <+> u)) [<]
  export
  prjL : {t, u : Ty} -> FullTerm ((t <+> u) ~> t) [<]
  export
  prjR : {t, u : Ty} -> FullTerm ((t <+> u) ~> u) [<]

  injL {t = N, u = N} = id
  injL {t = N, u = u ~> u'} = abs' (S $ S Z) (\n, _ => app (lift (prjR . injL)) n)
  injL {t = t ~> t', u = N} = id
  injL {t = t ~> t', u = u ~> u'} = abs' (S Z) (\f => drop injL . f . drop prjL)

  injR = swap . injL

  prjL {t = N, u = N} = id
  prjL {t = N, u = u ~> u'} = abs' (S Z) (\f => app (drop (prjL . injR) . f) (drop arb))
  prjL {t = t ~> t', u = N} = id
  prjL {t = t ~> t', u = u ~> u'} = abs' (S Z) (\f => drop prjL . f . drop injL)

  prjR = prjL . swap

namespace Unit
  export
  Unit : Ty
  Unit = N

namespace Pair
  export
  (*) : Ty -> Ty -> Ty
  t * u = B ~> (t <+> u)

  export
  pair : {t, u : Ty} -> FullTerm (t ~> u ~> (t * u)) [<]
  pair = abs' (S $ S $ S Z)
    (\fst, snd, b => app' (lift if') [<b, app (lift injL) fst, app (lift injR) snd])

  export
  fst : {t, u : Ty} -> FullTerm ((t * u) ~> t) [<]
  fst = abs' (S Z) (\p => app (drop prjL . p) (drop true))

  export
  snd : {t, u : Ty} -> FullTerm ((t * u) ~> u) [<]
  snd = abs' (S Z) (\p => app (drop prjR . p) (drop false))

  export
  mapSnd : {t, u, v : Ty} -> FullTerm ((u ~> v) ~> (t * u) ~> (t * v)) [<]
  mapSnd = abs' (S $ S Z) (\f, p => app' (lift pair) [<app (lift fst) p , app (f . lift snd) p])

  export
  Product : SnocList Ty -> Ty
  Product = foldl (*) Unit

  export
  pair' : {tys : SnocList Ty} -> FullTerm (tys ~>* Product tys) [<]
  pair' {tys = [<]} = arb
  pair' {tys = tys :< ty} = abs' (S $ S Z) (\p, t => app' (lift pair) [<p, t]) .* pair'

  export
  project : {tys : SnocList Ty} -> Elem ty tys -> FullTerm (Product tys ~> ty) [<]
  project {tys = tys :< ty} Here = snd
  project {tys = tys :< ty} (There i) = project i . fst

  export
  mapProd :
    {ctx, tys, tys' : SnocList Ty} ->
    {auto 0 prf : SnocList.length tys = SnocList.length tys'} ->
    All (flip FullTerm ctx) (zipWith (~>) tys tys') ->
    FullTerm (Product tys ~> Product tys') ctx
  mapProd {tys = [<], tys' = [<]} [<] = lift id
  mapProd {tys = tys :< ty, tys' = tys' :< ty', prf} (fs :< f) =
    abs' (S Z)
      (\p =>
        app' (lift pair)
          [<app (drop (mapProd fs {prf = injective prf}) . lift fst) p
          , app (drop f . lift snd) p
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
    FullTerm ((ty ~> ty') ~> Vect n ty ~> Vect n ty') [<]
  mapVect =
    abs' (S Z)
      (\f => mapProd {prf = trans (replicateLen n) (sym $ replicateLen n)} $ zipReplicate f)

  export
  nil : {ty : Ty} -> FullTerm (Vect 0 ty) [<]
  nil = arb

  export
  cons : {n : Nat} -> {ty : Ty} -> FullTerm (ty ~> Vect n ty ~> Vect (S n) ty) [<]
  cons = abs' (S $ S Z) (\t, ts => app' (lift pair) [<ts, t])

  export
  head : {n : Nat} -> {ty : Ty} -> FullTerm (Vect (S n) ty ~> ty) [<]
  head = snd

  export
  tail : {n : Nat} -> {ty : Ty} -> FullTerm (Vect (S n) ty ~> Vect n ty) [<]
  tail = fst

  export
  index : {n : Nat} -> {ty : Ty} -> (i : Fin n) -> FullTerm (Vect n ty ~> ty) [<]
  index FZ = head
  index (FS i) = index i . tail

  export
  enumerate : (n : Nat) -> FullTerm (Vect n N) [<]
  enumerate 0 = arb
  enumerate (S k) = app' pair [<app' mapVect [<abs' (S Z) suc, enumerate k], zero]

namespace Sum
  export
  (+) : Ty -> Ty -> Ty
  t + u = B * (t <+> u)

  export
  left : {t, u : Ty} -> FullTerm (t ~> (t + u)) [<]
  left = abs' (S Z) (\e => app' (drop pair) [<drop true, app (drop injL) e])

  export
  right : {t, u : Ty} -> FullTerm (u ~> (t + u)) [<]
  right = abs' (S Z) (\e => app' (drop pair) [<drop false, app (drop injR) e])

  export
  case' : {t, u, ty : Ty} -> FullTerm ((t + u) ~> (t ~> ty) ~> (u ~> ty) ~> ty) [<]
  case' = abs' (S $ S $ S Z)
    (\s, f, g =>
      app' (lift if')
        [<app (lift fst) s
        , app (f . lift (prjL . snd)) s
        , app (g . lift (prjR . snd)) s])

  export
  either : {t, u, ty : Ty} -> FullTerm ((t ~> ty) ~> (u ~> ty) ~> (t + u) ~> ty) [<]
  either = abs' (S $ S $ S Z) (\f, g, s => app' (lift case') [<s, f, g])

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
    FullTerm (ty ~> Sum' ty' tys) [<]
  put' {tys = []} Here = id
  put' {tys = _ :: _} Here = left
  put' {tys = _ :: _} (There i) = right . put' i

  export
  put : {tys : List1 Ty} -> {ty : Ty} -> (i : Elem ty (forget tys)) -> FullTerm (ty ~> Sum tys) [<]
  put {tys = _ ::: _} i = put' i

  any' :
    {ctx : SnocList Ty} ->
    {ty, ty' : Ty} ->
    {tys : List Ty} ->
    All (flip FullTerm ctx . (~> ty)) (ty' :: tys) ->
    FullTerm (Sum' ty' tys ~> ty) ctx
  any' (t :: []) = t
  any' (t :: u :: ts) = app' (lift either) [<t, any' (u :: ts)]

  export
  any :
    {ctx : SnocList Ty} ->
    {tys : List1 Ty} ->
    {ty : Ty} ->
    All (flip FullTerm ctx . (~> ty)) (forget tys) ->
    FullTerm (Sum tys ~> ty) ctx
  any {tys = _ ::: _} = any'

namespace Nat
  export
  isZero : FullTerm (N ~> B) [<]
  isZero = abs' (S Z) (\m => rec m (drop true) (abs (lift false)))

  export
  add : FullTerm (N ~> N ~> N) [<]
  add = abs' (S $ S Z) (\m, n => rec m n (abs' (S Z) suc))

  export
  sum : {n : Nat} -> FullTerm (Vect n N ~> N) [<]
  sum {n = 0} = abs zero
  sum {n = S k} = abs' (S Z)
    (\ns => app' (lift add) [<app (lift head) ns, app (lift (sum . tail)) ns])

  export
  pred : FullTerm (N ~> N) [<]
  pred = abs' (S Z)
    (\m =>
      app' (lift case')
        [<rec m
            (lift $ app left (arb {ty = Unit}))
            (app' (lift either)
              [<abs (lift $ app right zero)
              , abs' (S Z) (\n => app (lift right) (suc n))
              ])
        , abs zero
        , drop id
        ])

  export
  sub : FullTerm (N ~> N ~> N) [<]
  sub = abs' (S $ S Z) (\m, n => rec n m (lift pred))

  export
  le : FullTerm (N ~> N ~> B) [<]
  le = abs' (S Z) (\m => lift isZero . app (lift sub) m)

  export
  lt : FullTerm (N ~> N ~> B) [<]
  lt = abs' (S Z) (\m => app (lift le) (suc m))

  export
  cond :
    {ctx : SnocList Ty} ->
    {ty : Ty} ->
    List (FullTerm N ctx, FullTerm (N ~> ty) ctx) ->
    FullTerm (N ~> ty) ctx
  cond [] = lift arb
  cond ((n, v) :: xs) =
    abs' (S Z)
      (\t =>
        app' (lift if')
          [<app' (lift le) [<t, drop n]
          , app (drop v) t
          , app (drop $ cond xs) (app' (lift sub) [<t, drop n])])

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
    FullTerm ((ty ~> ty') ~> fillShape shape ty ~> fillShape shape ty') [<]
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
    (ts : FullTerm (Vect n (fix c)) ctx) ->
    (acc : FullTerm N ctx) ->
    List (FullTerm N ctx, FullTerm (N ~> N) ctx)
  calcOffsets {n = 0} ts acc = []
  calcOffsets {n = S k} ts acc =
    let hd = app (lift head) ts in
    let n = app (lift $ project $ There $ There Here) hd in
    let offset = app (lift $ project $ There Here) hd in
    (n, app (lift add) acc . offset) ::
    calcOffsets
      (app (lift tail) ts)
      (app' (lift add) [<suc n, acc])

  calcData :
    {ctx : SnocList Ty} ->
    {c : Container} ->
    {n : Nat} ->
    (ts : FullTerm (Vect n (fix c)) ctx) ->
    (acc : FullTerm N ctx) ->
    List (FullTerm N ctx, FullTerm (N ~> fill c N) ctx)
  calcData {n = 0} ts acc = []
  calcData {n = S k} ts acc =
    let hd = app (lift head) ts in
    let n = app (lift $ project $ There $ There Here) hd in
    (n, app (lift $ project Here) hd) ::
    calcData
      (app (lift tail) ts)
      (app' (lift add) [<suc n, acc])

  export
  intro :
    {c : Container} ->
    {shape : Shape} ->
    Elem shape (forget c) ->
    FullTerm (fillShape shape (fix c) ~> fix c) [<]
  intro {shape = (shape, n)} i = abs' (S Z)
    (\t =>
      app' (lift $ pair' {tys = [<N, N ~> N, N ~> fill c N]})
        [<app (lift (sum . app mapVect (abs' (S Z) suc . project (There $ There Here)) . snd)) t
        , cond ((zero, abs' (S Z) suc) :: calcOffsets (app (lift snd) t) (suc zero))
        , cond
          (  (zero,
              abs
                (app
                  (lift $ put {tys = map (flip fillShape N) c} $
                    rewrite forgetMap (flip fillShape N) c in
                    elemMap (flip fillShape N) i)
                  (app' (lift mapSnd) [<abs (lift $ enumerate n), drop t])))
          :: calcData (app (lift snd) t) (suc zero)
          )
        ])

  export
  elim :
    {c : Container} ->
    {ctx : SnocList Ty} ->
    {ty : Ty} ->
    All (flip FullTerm ctx . (~> ty) . flip Data.fillShape ty) (forget c) ->
    FullTerm (fix c ~> ty) ctx
  elim cases = abs' (S Z)
    (\t =>
      let tags = suc (app (lift $ project $ There $ There Here) t) in
      let offset = app (lift $ project $ There Here) (drop $ drop t) in
      let vals = app (lift $ project $ Here) (drop $ drop t) in
      app'
        (rec tags
          (lift arb)
          (abs' (S $ S Z) (\rec, n =>
            app
              (any {tys = map (flip fillShape N) c}
                (rewrite forgetMap (flip fillShape N) c in
                 gmap
                   (\f =>
                     drop (drop $ drop f) .
                     app (lift mapShape) (rec . app (lift add) (app offset n)))
                   cases) .
               vals)
              n)))
        [<zero])

  -- elim cases (#tags-1,offset,data) =
  --   let
  --       step : (N -> ty) -> (N -> ty)
  --       step rec n =
  --         case rec n of
  --           i => cases(i) . mapShape (rec . (+ offset n))
  --   in
  --       rec #tags arb step 0
