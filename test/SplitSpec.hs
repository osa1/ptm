module SplitSpec where

import qualified Data.Map as M

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit

import CoreLike.Eval
import CoreLike.Syntax

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    fromHUnitTest scByEvalExs


-- | Some examples taken from the paper "Supercompilation by Evaluation"
scByEvalExs :: Test
scByEvalExs = TestLabel "Examples from \"Supercompilation by Evalution\"" $ TestList
  [ TestLabel "split (Just y)" $
    let env = M.fromList [ ("x", Value $ Literal $ Int 1)
                         , ("y", PrimOp Add [Var "x", Var "x"])
                         ] in
    fst <$> (split (Value $ Data "Just" ["y"], env, [])) ~=?
    Just [ (Var "y", env, []) ]
  ]
