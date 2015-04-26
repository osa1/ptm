module TestUtils where

import Control.DeepSeq
import qualified Control.Exception as E

import Test.HUnit.Lang

type Assertion' = IO

assertFailure' :: String -> Assertion' a
assertFailure' msg = msg `deepseq` E.throwIO (HUnitFailure msg)

fromRight :: Show a => Either a b -> b
fromRight (Right r) = r
fromRight (Left l)  = error $ "fromRight: found Left: " ++ show l