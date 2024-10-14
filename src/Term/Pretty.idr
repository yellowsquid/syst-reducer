module Term.Pretty

import public Text.PrettyPrint.Prettyprinter
import public Text.PrettyPrint.Prettyprinter.Render.Terminal

import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Stream
import Data.String

import Term
import Term.Syntax

%prefix_record_projections off

data Syntax = Bound | Keyword | Symbol | Literal

symbol : Doc Syntax -> Doc Syntax
symbol = annotate Symbol

keyword : Doc Syntax -> Doc Syntax
keyword = annotate Keyword

bound : Doc Syntax -> Doc Syntax
bound = annotate Bound

literal : Doc Syntax -> Doc Syntax
literal = annotate Literal

rec_ : Doc Syntax
rec_ = keyword "rec"

underscore : Doc Syntax
underscore = bound "_"

arrow : Doc Syntax
arrow = symbol "=>"

backslash : Doc Syntax
backslash = symbol Symbols.backslash

lit : Nat -> Doc Syntax
lit = literal . pretty

public export
interface Renderable (0 a : Type) where
  fromSyntax : Syntax -> a

export
Renderable () where
  fromSyntax _ = ()

export
Renderable AnsiStyle where
  fromSyntax Bound = italic
  fromSyntax Keyword  = color Blue
  fromSyntax Symbol = color BrightWhite
  fromSyntax Literal = color Green

startPrec, leftAppPrec, appPrec : Prec
startPrec = Open
leftAppPrec = Equal
appPrec = App

data StrictThins : SnocList a -> SnocList a -> Type where
  Empty : [<] `StrictThins` [<]
  Drop : sx `StrictThins` sy -> sx `StrictThins` sy :< y
  Keep : sx `StrictThins` sy -> sx :< z `StrictThins` sy :< z

%name StrictThins thin

record IsBound (ty : Ty) (ctx : SnocList Ty) (t : FullTerm ty' ctx') where
  constructor MkBound
  {0 bound : SnocList Ty}
  {0 used : SnocList Ty}
  thin : used `StrictThins` bound
  0 prfTy : ty = bound ~>* ty'
  0 prfCtx : ctx' = ctx ++ used

%name IsBound isBound

record Binding (ty : Ty) (ctx : SnocList Ty) where
  constructor MkBinding
  {0 ty' : Ty}
  {0 ctx' : SnocList Ty}
  term : FullTerm ty' ctx'
  isBound : IsBound ty ctx term

%name Binding bound

getBinding : (t : FullTerm ty' ctx') -> IsBound ty ctx t -> Binding ty ctx
getBinding (Const t) isBound =
  getBinding t (MkBound (Drop isBound.thin) isBound.prfTy isBound.prfCtx)
getBinding (Abs {ty} t) isBound =
  getBinding t (MkBound (Keep isBound.thin) isBound.prfTy (cong (:< ty) isBound.prfCtx))
getBinding t isBound = MkBinding t isBound

isBoundRefl : (0 t : FullTerm ty ctx) -> IsBound ty ctx t
isBoundRefl t = MkBound {bound = [<]} Empty Refl Refl

record Spline (ty : Ty) (ctx : SnocList Ty) where
  constructor MkSpline
  {0 tys : SnocList Ty}
  head : Term (tys ~>* ty) ctx
  args : All (flip Term ctx) tys

%name Spline spline

wkn : Spline ty ctx -> ctx `Thins` ctx' -> Spline ty ctx'
wkn spline thin = MkSpline (wkn spline.head thin) (mapProperty (flip wkn thin) spline.args)

getSpline : FullTerm ty ctx -> Spline ty ctx
getSpline (App (MakePair (t `Over` thin) u _)) =
  let rec = wkn (getSpline t) thin in
  MkSpline rec.head (rec.args :< u)
getSpline t = MkSpline (t `Over` Id) [<]

public export
data Len : SnocList a -> Type where
  Z : Len [<]
  S : Len sx -> Len (sx :< a)

%name Len k

export
lenToNat : Len sx -> Nat
lenToNat Z = 0
lenToNat (S k) = S (lenToNat k)

lenSrc : sx `StrictThins` sy -> Len sx
lenSrc Empty = Z
lenSrc (Drop thin) = lenSrc thin
lenSrc (Keep thin) = S (lenSrc thin)

strictSrc : Len sz -> sx `StrictThins` sy  -> Len (sz ++ sx)
strictSrc k Empty = k
strictSrc k (Drop thin) = strictSrc k thin
strictSrc k (Keep thin) = S (strictSrc k thin)

extend : sx `Thins` sy -> Len sz -> sx ++ sz `Thins` sy ++ sz
extend thin Z = thin
extend thin (S k) = Keep (extend thin k)

public export
prettyOp : Operator tys ty -> Doc Syntax
prettyOp (Lit n) = lit n
prettyOp Suc = keyword "suc"
prettyOp Plus = keyword "plus"
prettyOp Mult = keyword "mult"
prettyOp Pred = keyword "pred"
prettyOp Minus = keyword "minus"
prettyOp Div = keyword "div"
prettyOp Mod = keyword "mod"
-- prettyOp (Inl _ _) = keyword "inl"
-- prettyOp (Inr _ _) = keyword "inr"
-- prettyOp (Prl _ _) = keyword "prl"
-- prettyOp (Prr _ _) = keyword "prr"

parameters (names : Stream String)
  prettyTerm' : (len : Len ctx) => Prec -> Term ty ctx -> Doc Syntax
  prettyFullTerm : (len : Len ctx) => Prec -> FullTerm ty ctx' -> ctx' `Thins` ctx -> Doc Syntax
  prettyBinding : (len : Len ctx) => Prec -> Binding ty ctx' -> ctx' `Thins` ctx -> Doc Syntax
  prettySpline : (len : Len ctx) => Prec -> Spline ty ctx -> Doc Syntax

  prettyTerm' d (t `Over` thin) = prettyFullTerm d t thin

  prettyFullTerm d Var thin =
    bound (pretty $ index (minus (lenToNat len) (S $ elemToNat $ index thin Here)) names)
  prettyFullTerm d t@(Const _) thin =
    prettyBinding d (assert_smaller t $ getBinding t $ isBoundRefl t) thin
  prettyFullTerm d t@(Abs _) thin =
    prettyBinding d (assert_smaller t $ getBinding t $ isBoundRefl t) thin
  prettyFullTerm d t@(App _) thin =
    prettySpline d (assert_smaller t $ wkn (getSpline t) thin)
  prettyFullTerm d (Op op) thin = prettyOp op
  prettyFullTerm d t@(Rec _) thin =
    prettySpline d (assert_smaller t $ wkn (getSpline t) thin)

  prettyBinding d (MkBinding t {ctx' = ctx'_} (MkBound thin' _ prfCtx)) thin =
    parenthesise (d > startPrec) $ group $ align $ hang 2 $
      Pretty.backslash <+> snd (prettyThin (lenToNat len) thin') <++> arrow <+> line <+>
        prettyFullTerm @{strictSrc len thin'} Open t
          (rewrite prfCtx in extend thin $ lenSrc thin')
    where
    prettyThin : Nat -> sx `StrictThins` sy -> (Nat, Doc Syntax)
    prettyThin n Empty = (n, neutral)
    prettyThin n (Drop Empty) = (n, underscore)
    prettyThin n (Keep Empty) = (S n, bound (pretty $ index n names))
    prettyThin n (Drop thin) =
      let (k, doc) = prettyThin n thin in
      (k, doc <+> comma <++> underscore)
    prettyThin n (Keep thin) =
      let (k, doc) = prettyThin n thin in
      (S k, doc <+> comma <++> bound (pretty $ index k names))

  prettySpline d
    (MkSpline (Rec (MakePair t (MakePair u v _ `Over` thin2) _) `Over` thin1) args) =
      parenthesise (d >= appPrec) $ group $ align $ hang 2 $
        (rec_ <++> assert_total (prettyTerm' appPrec (wkn t thin1))) <+> line <+>
        vsep
          ([assert_total $ prettyTerm' appPrec (wkn u (thin1 . thin2))
          , assert_total $ prettyTerm' appPrec (wkn v (thin1 . thin2))] ++
            toList (forget $ mapProperty (assert_total $ prettyTerm' appPrec) args))
  prettySpline d s@(MkSpline t args) =
    parenthesise (d >= appPrec) $ group $ align $ hang 2 $
      prettyTerm' leftAppPrec t <+> line <+>
      vsep (toList $ forget $ mapProperty (assert_total $ prettyTerm' appPrec) args)

finToChar : Fin 26 -> Char
finToChar 0 = 'x'
finToChar 1 = 'y'
finToChar 2 = 'z'
finToChar 3 = 'a'
finToChar 4 = 'b'
finToChar 5 = 'c'
finToChar 6 = 'd'
finToChar 7 = 'e'
finToChar 8 = 'f'
finToChar 9 = 'g'
finToChar 10 = 'h'
finToChar 11 = 'i'
finToChar 12 = 'j'
finToChar 13 = 'k'
finToChar 14 = 'l'
finToChar 15 = 'm'
finToChar 16 = 'n'
finToChar 17 = 'o'
finToChar 18 = 'p'
finToChar 19 = 'q'
finToChar 20 = 'r'
finToChar 21 = 's'
finToChar 22 = 't'
finToChar 23 = 'u'
finToChar 24 = 'v'
finToChar 25 = 'w'

name : Nat -> List Char
name k =
  case divMod k 26 of
    Fraction k 26 0 r prf => [finToChar r]
    Fraction k 26 (S q) r prf => finToChar r :: name (assert_smaller k q)

export
canonicalNames : Stream String
canonicalNames = map (fastPack . reverse . name) nats

export
prettyTerm : Renderable ann => (len : Len ctx) => Term ty ctx -> Doc ann
prettyTerm t = map fromSyntax (prettyTerm' canonicalNames Open t)
