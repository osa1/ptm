module TestUtils where

import Control.DeepSeq
import qualified Control.Exception as E
import Control.Monad (unless)

import Test.HUnit.Lang

type Assertion' = IO

assertFailure' :: String -> Assertion' a
assertFailure' msg = msg `deepseq` E.throwIO (HUnitFailure msg)

-- | Like HUnit's 'assertEqual', except takes strings to be used in case of a
-- failure.
assertEqStrs :: Eq a => String -> a -> a -> String -> String -> Assertion
assertEqStrs preface expected actual expectedStr actualStr =
    unless (expected == actual) (assertFailure msg)
  where
    msg = (if null preface then "" else preface ++ "\n") ++
          "expected: " ++ expectedStr ++ "\n but got: " ++ actualStr

fromRight :: Show a => Either a b -> b
fromRight (Right r) = r
fromRight (Left l)  = error $ "fromRight: found Left: " ++ show l
