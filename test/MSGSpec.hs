{-# LANGUAGE ViewPatterns #-}

module MSGSpec where

import qualified Data.Map as M

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit

import TestUtils

import CoreLike.MSG
import CoreLike.Parser
import CoreLike.Syntax
import CoreLike.Utils (showPretty)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "MSG" $ do
      fromHUnitTest $ assertMsg "x" "y"
      fromHUnitTest $ assertMsg "x" "x"
      fromHUnitTest $ assertMsg "(a, b)" "(x, y)"

assertMsg :: String -> String -> Test
assertMsg s1 s2 =
    TestLabel ("msg of " ++ s1 ++ " and " ++ s2) $ TestCase $ do
      t1  <- parseAssert s1
      t2  <- parseAssert s2
      msg <- assertJust (msg' t1 t2)
      msgProps t1 t2 msg

msgProps :: Term' -> Term' -> (Subst', Term', Subst') -> Assertion
msgProps t1 t2 msg@(M.toList -> t1_s, t, M.toList -> t2_s) = do
    -- property 1: Applying substitutions to t should give t1 and t2
    let msg_t1 = substTerms t1_s t
        msg_t2 = substTerms t2_s t

    assertEqStrs errMsg t1 msg_t1 (showPretty t1) (showPretty msg_t1)
    assertEqStrs errMsg t2 msg_t2 (showPretty t2) (showPretty msg_t2)
  where
    errMsg = "MSG + substitutions does not give us the term.\n" ++ msgFailMsg msg


msgFailMsg :: (Subst', Term', Subst') -> String
msgFailMsg (M.toList -> s1, t, M.toList -> s2) = unlines
  [ "Term: ", showPretty t
  , "Left substitutions:\n" ++ showPretty s1
  , "Right substitutions:\n" ++ showPretty s2
  ]
