-- Disabling this until all tests are fixed/re-implemented:
{- OPTIONS_GHC -F -pgmF hspec-discover #-}

module Main where

import qualified EvalSpec
import qualified ParserSpec

import Test.Hspec

main :: IO ()
main = hspec $ sequence_ [ ParserSpec.spec, EvalSpec.spec ]
