module Encoded.Test

import Data.Stream
import Data.String

import Encoded.Arith
import Encoded.Container
import Encoded.Fin
import Encoded.Pair
import Encoded.Sum
import Encoded.Term
import Encoded.Vect

import System

import Term.Compile
import Term.Pretty
import Term.Syntax
import Term.Semantics

import Text.PrettyPrint.Prettyprinter.Render.String

%ambiguity_depth 4

-- ListC : Ty -> Container
-- ListC ty = Cases [<(Nothing, 0), (Just ty, 1)]

-- List : Ty -> Ty
-- List = W . ListC

-- nil : {ty : Ty} -> Term (List ty) ctx
-- nil = App (intro . tag (There Here)) [<Vect.nil {ty = List ty}]

-- cons : {ty : Ty} -> Term (ty ~> List ty ~> List ty) ctx
-- cons = AbsAll [<_, _] (\[<x, xs] =>
--   App (intro . tag @{IsSnoc} Here) [<App pair [<x, App Vect.cons [<xs, Vect.nil]]])

-- sum : Term (List N ~> N) ctx
-- sum = App (elim {c = ListC N})
--   [<Const 0
--   , Abs' (\x => App fst x + App index [<App snd [<x], zero])
--   ]

-- fromList' : List Nat -> Term (List N) [<List N, N ~> List N ~> List N]
-- fromList' [] = Var (There Here)
-- fromList' (x :: xs) = App (Var Here) [<Op (Lit x), fromList' xs]

-- fromList : List Nat -> Term (List N) [<]
-- fromList xs = App (Abs $ Abs $ fromList' xs) [<Test.nil, Test.cons]

%inline
layoutOptions : LayoutOptions
layoutOptions = MkLayoutOptions (AvailablePerLine 213 0.5)

data Mode = Color | NoColor | FastCompile | Compile | Profile

%inline
render : Len ctx => Mode -> Term ty ctx -> IO ()
render Color t =
  Terminal.renderIO $
  layoutSmart layoutOptions $ prettyTerm t
render NoColor t =
  String.renderIO $
  layoutSmart layoutOptions $ prettyTerm {ann = ()} t
render _ t = pure ()

NeedShow : Mode -> Ty -> Type
NeedShow FastCompile = const ()
NeedShow Compile = const ()
NeedShow Profile = const ()
NeedShow _ = Show . TypeOf

run : (m : Mode) -> NeedShow m ty => Len ctx => Term ty ctx -> All TypeOf ctx -> IO ()
run FastCompile t args =
  putStrLn $
  renderShow (layoutCompact $ compileTerm {ann = ()} Run t) ""
run Compile t args =
  putStrLn $
  renderShow (layoutSmart layoutOptions $ compileTerm {ann = ()} Run t) ""
run Profile t args =
  putStrLn $
  renderShow (layoutSmart layoutOptions $ compileTerm {ann = ()} Profile t) ""
run Color t args = printLn (sem t args)
run NoColor t args = printLn (sem t args)

parseArgs : List String -> IO (Mode, Nat, Nat)
parseArgs [_, "--color", k, n] = pure (Color, stringToNatOrZ k, stringToNatOrZ n)
parseArgs [_, "--no-color", k, n] = pure (NoColor, stringToNatOrZ k, stringToNatOrZ n)
parseArgs [_, "--fast-compile", k, n] = pure (FastCompile, stringToNatOrZ k, stringToNatOrZ n)
parseArgs [_, "--compile", k, n] = pure (Compile, stringToNatOrZ k, stringToNatOrZ n)
parseArgs [_, "--profile", k, n] = pure (Profile, stringToNatOrZ k, stringToNatOrZ n)
parseArgs [_, k, n] = pure (Compile, stringToNatOrZ k, stringToNatOrZ n)
parseArgs _ = do putStrLn "Bad arguments"; exitFailure

lit : Term (N ~> Term) ctx
lit = Abs' (\n => Rec n Zero Suc)

add : Term (N ~> N ~> Term) ctx
add = AbsAll [<_,_] (\[<k, n] =>
  App Rec [<App lit [<k], App lit [<n], App (Abs . Suc . Var) [<0]])

AssumeNat : Eliminator N ctx
AssumeNat =
  MkElim
    { var = Arb
    , zero = 0
    , suc = Op Suc
    , rec = Arb
    , abs = Arb
    , app = Arb
    }

main : IO ()
main = do
  args <- getArgs
  (mode, k, n) <- parseArgs args
  -- printLn (size $ reduce {ctx = [<]})
  render {ctx = [<]} mode reduce

  -- let t : Term Term [<] = App reduce [<65536, App add [<2, 3]]
  -- run FastCompile t [<]

  -- let ns = take n nats
  -- let t : Term (List N) [<] = fromList ns
  -- let t : Term N [<] = App sum [<t]
