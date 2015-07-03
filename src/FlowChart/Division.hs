-- | This module implements binding-time analysis(BTA) as described in
-- section 4.4.6.
--
-- In this language we don't have lexical scoping, we have only one scope which
-- contains all variables in the program.

module FlowChart.Division where

import qualified Data.Set as S
import Control.Monad.State

import FlowChart.Syntax

data Division = Division
  { statics  :: S.Set Var
  , dynamics :: S.Set Var
  } deriving (Show, Eq)

initDivision :: Division -> Program -> Division
initDivision (Division ss ds) pgm =
    -- unspecified variables are marked as dynamic
    let otherVars = allVars pgm `S.difference` S.union ss ds in
    Division ss (ds `S.union` otherVars)

congruentDivision :: Division -> Program -> Division
congruentDivision d pgm =
    if d' == d then d else congruentDivision d' pgm
  where
    d' = execState (step pgm) d

step :: Program -> State Division ()
step (Program _ bs) = mapM_ stepBlock bs
  where
    stepBlock (BasicBlock _ asgns _) = mapM_ stepAsgn asgns
    stepAsgn (Assignment v e) = do
      dyns <- gets dynamics
      unless (S.null $ expVars e `S.intersection` dyns) $ do
        modify $ \(Division ss ds) -> Division (S.delete v ss) (S.insert v ds)

--------------------------------------------------------------------------------

allVars :: Program -> S.Set Var
allVars (Program vs bs) = S.unions $ S.fromList vs : map blockVs bs

blockVs :: BasicBlock -> S.Set Var
blockVs (BasicBlock _ asgns _) = S.unions $ map asgnVars asgns

asgnVars :: Assignment -> S.Set Var
asgnVars (Assignment v e) = S.insert v $ expVars e

expVars :: Expr -> S.Set Var
expVars Constant{} = S.empty
expVars (Var v)    = S.singleton v
expVars (Op _ es)  = S.unions $ map expVars es
