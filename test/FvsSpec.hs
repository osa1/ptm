{-# LANGUAGE MultiWayIf, TupleSections #-}

module FvsSpec where

import qualified Data.Set as S

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit

import CoreLike.Parser
import CoreLike.Syntax

main :: IO ()
main = hspec spec

fromRight (Right r) = r
fromRight (Left l)  = error $ "fromRight: found Left: " ++ show l

spec :: Spec
spec = do
    fromHUnitTest $ TestList
      [ TestCase $ fvsEq "\\a -> a + b" ["+", "b"]
      , TestCase $ fvsEq "case x of A a -> f a b; y -> x + y; _ -> z" ["+", "f", "x", "b", "z"]
      ]

fvsEq :: String -> [Var] -> Assertion
fvsEq term fvs =
    assertEqual "fvs are not equal" (fvsTerm (fromRight (parseTerm term))) (S.fromList fvs)
