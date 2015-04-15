{-# LANGUAGE MultiWayIf, TupleSections #-}

module SubstSpec where

import Control.Monad
import qualified Data.Set as S
import qualified Language.Haskell.Exts as HSE

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
        , substEq "let2" "let x = y in x + y" "y" "x" "let x = x in x + x"
          -- FIXME: Several issues here:
          --   - Need to do alpha renaming.
          --   - Need a "equality modulo alpha-renaming" test. (because we
          --     introduce new let bindings)
          --   - We may need to float lets to outer levels as much as possible.
        , substEq "case1" "case x of { Blah a b -> a + b; y -> x + y }"
                          "x" "Data x y"
                          "case Data x y of { Blah a b -> a + b; y -> (let x = Data x y in (+) x) y }"
          -- FIXME: We again need renaming here.
        , substEq "case simple 1" "case x of { y -> x + y }"
                                  "x" "y"
                                  "case y of { v0 -> y + v0 }"
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
substEq name t v t' exp = TestLabel name $ TestCase $ do
    tm       <- term t
    newTm    <- term t'
    expected <- term exp
    let s = substTerm v newTm tm
    unless (s == expected) $
      assertFailure $ unlines
        [ "Substituted term is different than expected term."
        , "  Expected:"
        , HSE.prettyPrint (termToHSE expected)
        , "  Found:"
        , HSE.prettyPrint (termToHSE s)
        ]

term :: String -> Assertion' Term
term = either (assertFailure' . (++) "Can't parse str as term: ") return . parseTerm
