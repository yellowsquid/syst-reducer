module Total.Pretty

import public Text.PrettyPrint.Prettyprinter
import public Text.PrettyPrint.Prettyprinter.Render.Terminal

import Data.DPair
import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Stream
import Data.String

import Total.Syntax
import Total.Term

data Syntax = Bound | Keyword

keyword : Doc Syntax -> Doc Syntax
keyword = annotate Keyword

bound : Doc Syntax -> Doc Syntax
bound = annotate Bound

rec_ : Doc Syntax
rec_ = keyword "rec"

plus : Doc Syntax
plus = keyword "+"

arrow : Doc Syntax
arrow = keyword "=>"

public export
interface Renderable (0 a : Type) where
  fromSyntax : Syntax -> a

export
Renderable AnsiStyle where
  fromSyntax Bound    = italic
  fromSyntax Keyword  = color BrightWhite

startPrec, leftAppPrec, appPrec : Prec
startPrec = Open
leftAppPrec = Equal
appPrec = App

parameters (names : Stream String)
  export
  prettyTerm : Len ctx -> Prec -> Term ctx ty -> Doc Syntax
  prettyTerm len d (Var i) = bound (pretty $ index (minus (cast len) (S $ elemToNat i)) names)
  prettyTerm len d (Abs t) =
    let Evidence _ (len, t') = getLamNames (S len) t in
    parenthesise (d > startPrec) $ group $ align $ hang 2 $
      backslash <+> prettyBindings len <++> arrow <+> line <+>
        (prettyTerm len Open (assert_smaller t t'))
    where
    getLamNames :
      forall ctx, ty.
      Len ctx ->
      Term ctx ty ->
      Exists {type = Pair _ _} (\ctxTy => (Len (fst ctxTy), Term (fst ctxTy) (snd ctxTy)))
    getLamNames k (Abs t) = getLamNames (S k) t
    getLamNames k t@(Var _) = Evidence (_, _) (k, t)
    getLamNames k t@(App _ _) = Evidence (_, _) (k, t)
    getLamNames k t@Zero = Evidence (_, _) (k, t)
    getLamNames k t@(Suc _) = Evidence (_, _) (k, t)
    getLamNames k t@(Rec _ _ _) = Evidence (_, _) (k, t)

    prettyBindings' : Nat -> Nat -> Doc Syntax
    prettyBindings' offset 0 = neutral
    prettyBindings' offset 1 = bound (pretty $ index offset names)
    prettyBindings' offset (S (S k)) =
      bound (pretty $ index offset names) <+> comma <++> prettyBindings' (S offset) (S k)

    prettyBindings : Len ctx' -> Doc Syntax
    prettyBindings k = prettyBindings' (cast len) (minus (cast k) (cast len))
  prettyTerm len d app@(App t u) =
    let (f, ts) = getSpline t [prettyArg u] in
    parenthesise (d >= appPrec) $ group $ align $ hang 2 $
      f <+> line <+> vsep ts
    where
    prettyArg : forall ty. Term ctx ty -> Doc Syntax
    prettyArg v = prettyTerm len appPrec (assert_smaller app v)

    getSpline :
      forall ty, ty'.
      Term ctx (ty ~> ty') ->
      List (Doc Syntax) ->
      (Doc Syntax, List (Doc Syntax))
    getSpline (App t u) xs = getSpline t (prettyArg u :: xs)
    getSpline (Rec t u v) xs = (rec_ <++> prettyArg t, prettyArg u :: prettyArg v :: xs)
    getSpline t'@(Var _) xs = (prettyTerm len leftAppPrec (assert_smaller t t'), xs)
    getSpline t'@(Abs _) xs = (prettyTerm len leftAppPrec (assert_smaller t t'), xs)
  prettyTerm len d Zero = pretty 0
  prettyTerm len d (Suc t) = 
    let (lit, t') = getSucs t in
    case t' of
      Just t' =>
        parenthesise (d >= appPrec) $ group $
          pretty (S lit) <++> plus <++> prettyTerm len leftAppPrec (assert_smaller t t')
      Nothing => pretty (S lit)
    where
    getSucs : Term ctx N -> (Nat, Maybe (Term ctx N))
    getSucs Zero = (0, Nothing)
    getSucs (Suc t) = mapFst S (getSucs t)
    getSucs t@(Var _) = (0, Just t)
    getSucs t@(App _ _) = (0, Just t)
    getSucs t@(Rec _ _ _) = (0, Just t)
  prettyTerm len d (Rec t u v) =
    parenthesise (d >= appPrec) $ group $ align $ hang 2 $
      rec_ <++>
      prettyTerm len appPrec t <+> line <+>
      prettyTerm len appPrec u <+> line <+>
      prettyTerm len appPrec v

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
canonicalNames = map (fastPack . name) nats

export
pretty : Renderable ann => (len : Len ctx) => Term ctx ty -> Doc ann
pretty t = map fromSyntax (prettyTerm canonicalNames len Open t)

-- \x, y, z =>
--   rec z
--     (\a, b => \c => \d => d (\d => d c) a x)
--     (\a => \b => b y)
--     0
--     (\x => x)
