-- | Closed programs should be evaluated to values using our step algorithm.
-- Also, `step` shouldn't return `Split` because in closed programs all branches
-- can be taken statically.
--
-- We test these properties here.
--
module EvalSpec where

import qualified Data.Map as M

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit

import CoreLike.Eval
import CoreLike.Parser
import CoreLike.Simplify
-- import CoreLike.Step
import CoreLike.Syntax
import TestUtils

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "evaluation" $ do
      env <- (M.fromList . fromRight) <$> runIO (parseModule <$> readFile "Prelude.hs")
      fromHUnitTest $ TestList $
        map (\p -> TestLabel p $ TestCase (bigStepNoSplit env p)) programs

isValue :: Term' -> Assertion
isValue Value{} = return ()
isValue (LetRec _ _ Value{}) = return ()
isValue notVal    = assertFailure (show notVal ++ " is not a value.")

parseAssert :: String -> Assertion' Term'
parseAssert s =
    case parseTerm s of
      Left err -> assertFailure ("Can't parse " ++ s ++ ": " ++ err) >> undefined
      Right tm -> return tm

bigStepNoSplit :: Env' -> String -> Assertion
bigStepNoSplit env s = do
    tm <- parseAssert s
    case eval (tm, env, []) of
      Nothing -> assertFailure "Can't evaluate term"
      Just ((tm', env', stack), updates) ->
        assertBool ("Stack is not empty:\n" ++ show (ppStack stack)) (null stack)

-- bigStepNoSplit :: Env -> String -> Assertion
-- bigStepNoSplit env term = iter (simpl $ parseTerm' term)
--   where
--     iter :: Term -> Assertion
--     iter t =
--       case step env t of
--         Transient t' -> iter $ simpl t'
--         Split _      -> assertFailure $ "`step` returned Split for term " ++ show t
--         Stuck        -> isValue t

programs :: [String]
programs =
  [ -- foldr based sum
    "sum []"
  , "sum [1, 2, 3]"
    -- foldl based sum
  , "let sum1 = foldl (\\a b -> a + b) 0 in sum1 [1, 2, 3]"
    -- recursive sum
  , "sum' []"
  , "sum' [1, 2, 3]"
    -- tail-recursive sum with accumulator
  , "sum'' 0 []"
  , "sum'' 0 [1, 2, 3]"
    -- mutually recursive even/odd implementation
  , "even 0"
  , "odd 1"
  , "even 10"
  , "odd 9"

  , "length []"
  , "length (map f [])" -- an open term that should terminate
  , "map f [1, 2, 3]"
  , "length (map f [1, 2, 3])"

  , "span f []" -- another open term, should terminate
  , "span odd [1,2,3]"

  , "reverse []"
  , "reverse [1, 2, 3]"
  ]
