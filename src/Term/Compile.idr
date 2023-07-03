module Term.Compile

import public Text.PrettyPrint.Prettyprinter

import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Stream
import Data.String

import Term
import Term.Syntax

%prefix_record_projections off

rec_ : Doc ann
rec_ = "my-rec"

underscore : Doc ann
underscore = "_"

plus : Doc ann
plus = "+"

lambda : Doc ann
lambda = "lambda"

lit : Nat -> Doc ann
lit = pretty

getSucs : FullTerm ty ctx -> (Nat, Maybe (FullTerm ty ctx))
getSucs (Lit n) = (n, Nothing)
getSucs (Suc t) = mapFst S (getSucs t)
getSucs t = (0, Just t)

public export
data Len : SnocList a -> Type where
  Z : Len [<]
  S : Len sx -> Len (sx :< a)

%name Len k

lenToNat : Len sx -> Nat
lenToNat Z = 0
lenToNat (S k) = S (lenToNat k)

extend : sx `Thins` sy -> Len sz -> sx ++ sz `Thins` sy ++ sz
extend thin Z = thin
extend thin (S k) = Keep (extend thin k)

parameters (names : Stream String)
  compileFullTerm : (len : Len ctx) => FullTerm ty ctx' -> ctx' `Thins` ctx -> Doc ann
  compileFullTerm Var thin =
    pretty $ index (minus (lenToNat len) (S $ elemToNat $ index thin Here)) names
  compileFullTerm (Const t) thin =
    parens $ group $ hang 2 $
      lambda <++> (parens $ underscore) <+> line <+>
      compileFullTerm t thin
  compileFullTerm (Abs t) thin =
    parens $ group $ hang 2 $
      lambda <++> (parens $ pretty $ index (lenToNat len) names) <+> line <+>
      compileFullTerm t (Keep thin)
  compileFullTerm (App (MakePair (t `Over` thin1) (u `Over` thin2) _)) thin =
    parens $ group $ align $
      compileFullTerm t (thin . thin1) <+> line <+>
      compileFullTerm u (thin . thin2)
  compileFullTerm (Lit n) thin = lit n
  compileFullTerm t'@(Suc t) thin =
    let (n, t) = getSucs t in
    case t of
      Just t =>
        parens $ group $ align $
          plus <++> lit (S n) <+> softline <+>
          compileFullTerm (assert_smaller t' t) thin
      Nothing => lit (S n)
  compileFullTerm
    (Rec (MakePair
      (t `Over` thin1)
      (MakePair (u `Over` thin2) (v `Over` thin3) _ `Over` thin') _))
    thin =
    parens $ group $ hang 2 $
      rec_ <++> compileFullTerm t (thin . thin1) <+> line <+>
        compileFullTerm u (thin . thin' . thin2) <+> line <+>
        compileFullTerm v (thin . thin' . thin3)

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

public export
data ProfileMode = Run | Profile

builtin_rec : String
builtin_rec = """
  (define (my-rec n z s)
    (let loop ((k 0) (acc z))
      (if (= k n)
        acc
        (loop (1+ k) (s acc)))))
  """

wrap_main : Len ctx => Term ty ctx -> Doc ann
wrap_main t =
  parens $ group $ hang 2 $
    "define (my-main)" <+> line <+>
      compileFullTerm canonicalNames t.value t.thin

run_main : ProfileMode -> String
run_main Run = """
  (display (my-main))
  (newline)
  """
run_main Profile = """
  (use-modules (statprof))
  (statprof my-main)
  """

export
compileTerm : Len ctx => ProfileMode -> Term ty ctx -> Doc ann
compileTerm mode t =
  pretty builtin_rec <+> hardline <+> hardline <+>
  wrap_main t <+> hardline <+> hardline <+>
  pretty (run_main mode)
