module Term.Compile

import public Text.PrettyPrint.Prettyprinter

import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Stream
import Data.String

import Term
import Term.Pretty
import Term.Syntax

%prefix_record_projections off

rec_ : Doc ann
rec_ = "squid-rec"

underscore : Doc ann
underscore = "_"

plus : Doc ann
plus = "+"

lambda : Doc ann
lambda = "lambda"

lit : Nat -> Doc ann
lit = pretty

compileOp : Operator tys ty -> Doc ann
compileOp (Lit n) = lit n
compileOp Suc = "1+"
compileOp Plus = "squid-plus"
compileOp Mult = "squid-mult"
compileOp Pred = "1-" -- Confusing name, but correct
compileOp Minus = "squid-minus"
compileOp Div = "squid-div"
compileOp Mod = "squid-mod"

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
  compileFullTerm (Op op) thin = compileOp op
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

public export
data ProfileMode = Run | Profile

builtins : String
builtins = """
  (define (squid-rec n z s)
    (let loop ((k 0) (acc z))
      (if (= k n)
        acc
        (loop (1+ k) (s acc)))))

  (define (squid-plus m) (lambda (n) (+ m n)))
  (define (squid-mult m) (lambda (n) (* m n)))
  (define (squid-minus m) (lambda (n) (- m n)))
  (define (squid-div m) (lambda (n) (euclidean-quotient m n)))
  (define (squid-mod m) (lambda (n) (euclidean-remainder m n)))
  """

wrap_main : Len ctx => Term ty ctx -> Doc ann
wrap_main t =
  parens $ group $ hang 2 $
    "define (squid-main)" <+> line <+>
      compileFullTerm canonicalNames t.value t.thin

run_main : ProfileMode -> String
run_main Run = """
  (display (squid-main))
  (newline)
  """
run_main Profile = """
  (use-modules (statprof))
  (statprof squid-main)
  """

export
compileTerm : Len ctx => ProfileMode -> Term ty ctx -> Doc ann
compileTerm mode t =
  pretty builtins <+> hardline <+> hardline <+>
  wrap_main t <+> hardline <+> hardline <+>
  pretty (run_main mode)
