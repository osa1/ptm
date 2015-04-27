module StepSpec where

import qualified Data.Map as M

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit

import CoreLike.Parser
import CoreLike.Simplify
import CoreLike.Step
import CoreLike.Syntax
import TestUtils

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    env <- (M.fromList . fromRight) <$> runIO (parseFile "Prelude.hs")
    describe "case name shadowing" $ do
      fromHUnitTest $ TestList
        [ TestCase $ stepEq env "let x = a : b in case x of { a : b -> b; _ -> x }" "b"
        , TestCase $ stepEq env "let b = 10 in let x = a : b in case x of { a : b -> b; _ -> x }" "10"
        ]

stepEq :: Env -> String -> String -> Assertion
stepEq env before after =
    assertEqual "Step returned wrong" (parseTerm' after) (stepTransient env $ parseTerm' before)
