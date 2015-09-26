module SubstSpec where

import Control.Monad
import qualified Language.Haskell.Exts as HSE
import Text.Groom (groom)

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit

import CoreLike.Parser
import CoreLike.Syntax
import CoreLike.ToHSE
import TestUtils

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "substitutions" $ do
      fromHUnitTest $ TestList
        [ substEq "lambda1" "\\x -> x" "x" "1 + 2" "\\x -> x"
        , substEq "let1" "let x = y in x + y" "x" "y" "let x = y in x + y"
        , substEq "let2" "let x = y in x + y" "y" "x" "let f0 = x in f0 + x"
          -- FIXME: Several issues here:
          --   - Need to do alpha renaming.
          --   - Need a "equality modulo alpha-renaming" test. (because we
          --     introduce new let bindings)
          --   - We may need to float lets to outer levels as much as possible.
        , -- FIXME: This one has a problem with parsing primops, namely, we
          -- parse it as if primop application requires A-normal form, which is
          -- not the case right now. We should probably decide whether we need
          -- A-normal form or not for primops.
          substEq "case1" "case x of { Blah a b -> a + b; y -> x + y }"
                          "x" "Data x y"
                          "case Data x y of { Blah a b -> a + b; y -> (Data x y) + y }"
        , substEq "case simple 1" "case x of { y -> x + y }"
                                  "x" "y"
                                  "case y of { f0 -> y + f0 }"
        , substEq "case simple 2" "case x of { y -> 1 + y }"
                                  "y" "10"
                                  "case x of { y -> 1 + y }"
        ]

substEq
  :: String -- ^ test name
  -> String -- ^ original term
  -> String -- ^ variable to substitute
  -> String -- ^ what to substitute to
  -> String -- ^ expected term
  -> Test
substEq name t v t' expr = TestLabel name $ TestCase $ do
    tm       <- term t
    newTm    <- term t'
    expected <- term expr
    let s = substTerm v newTm tm
    unless (s == expected) $
      assertFailure $ unlines
        [ "Substituted term is different than expected term."
        , "  Expected:"
        , HSE.prettyPrint (termToHSE expected)
        , parens (groom expected)
        , "  Found:"
        , HSE.prettyPrint (termToHSE s)
        , parens (groom s)
        ]
  where
    parens :: String -> String
    parens s = '(' : s ++ ")"

term :: String -> Assertion' Term
term = either (assertFailure' . (++) "Can't parse str as term: ") return . parseTerm
