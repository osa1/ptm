-- | Implementation of the `mix`(to be more specific, `mix1`, because this is
-- implemented in meta language) algorithm as described in Figure 4.7.
module FlowChart.Mix
  ( mix
  , Input
  ) where

import Control.Monad.State.Strict
import Data.Bifunctor (first)
import Data.List ((\\))
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Prelude hiding (div)
import Safe

import FlowChart.Division
import FlowChart.Syntax

type Input = M.Map Var Val

mix :: Program -> Division -> Input -> (Program, Label)
mix pgm@(Program r bs) div initialInput =
    let (BasicBlock entry _ _, st) =
          runState (loop (first_block, initialInput) pgm div) initPEState
        blocks = gcBlocks (map (\(Right b) -> b) $ M.elems $ peBlocks st) entry
     in (Program (r \\ S.toList (statics div)) blocks, entry)
  where
    first_block = headNote "mix: Program doesn't have any basic blocks." bs

data SD = S | D deriving (Show, Eq)

lookupDivision :: Division -> Var -> SD
lookupDivision (Division ss _) v = if S.member v ss then S else D

-- | Garbage collection for blocks -- remove unused blocks.
gcBlocks :: [BasicBlock] -> Label -> [BasicBlock]
gcBlocks bs0 entry = go [lookupBlock' bs0 entry]
  where
    go :: [BasicBlock] -> [BasicBlock]
    go bs =
      let usedLbls = map blockLbl bs
          jmpLbls  = S.fromList $ concatMap jumpLabels bs ++ usedLbls
       in if length bs == S.size jmpLbls
            then bs
            else go (map (lookupBlock' bs0) (S.toList jmpLbls))

    blockLbl (BasicBlock l _ _) = l

    jumpLabels :: BasicBlock -> [Label]
    jumpLabels (BasicBlock _ _ jmp) =
      case jmp of
        Nothing           -> []
        Just (Goto l)     -> [l]
        Just (If _ l1 l2) -> [l1, l2]
        Just Halt         -> []
        Just Panic{}      -> []

--------------------------------------------------------------------------------

data PEState = PEState
  { -- | A map of generated blocks for (label, known inputs) pairs. This is used for:
    --   1. Collecting generated blocks. 2. As `marked` in the paper.
    -- NOTE: We need to extend this before completing generating the BasicBlock to
    -- prevent loops.
    peBlocks   :: M.Map (Label, Input) (Either Label BasicBlock)
               -- NOTE:  ^^^^^ this should be original label, not a fresh one.
               -- Fresh label will be used in BasicBlock
               -- NOTE: Left in second argument means we have a loop.

  , -- | A counter for label generation.
    peLblCount :: Int
  } deriving (Show)

initPEState :: PEState
initPEState = PEState M.empty 0

genLabel :: Label -> Input -> State PEState Label
genLabel lbl _ = do
    c <- gets peLblCount
    modify $ \(PEState bs _) -> PEState bs (c + 1)
    return $ lbl ++ show c

addBlock :: Label -> Input -> Either Label BasicBlock -> State PEState ()
addBlock lbl input b =
    modify $ \(PEState bs c) -> PEState (M.insert (lbl, input) b bs) c

lookupVisitedBlock :: Label -> Input -> State PEState (Maybe (Either Label BasicBlock))
lookupVisitedBlock lbl input = do
    bs <- gets peBlocks
    return $ M.lookup (lbl, input) bs

lookupBlock :: Label -> Program -> BasicBlock
lookupBlock lbl (Program _ blocks) = lookupBlock' blocks lbl

lookupBlock' :: [BasicBlock] -> Label -> BasicBlock
lookupBlock' blocks lbl =
    findJustNote ("Label " ++ lbl ++ " is not in the program.")
                 (\(BasicBlock lbl' _ _) -> lbl == lbl') blocks

--------------------------------------------------------------------------------

-- FIXME: Rename this
loop :: (BasicBlock, Input)      -- ^ (pp, vs)
     -> Program                  -- ^ program to lookup basic blocks
     -> Division                 -- ^ BTA, static/dynamic division of variables
                                 --   in current pp
     -> State PEState BasicBlock
loop (BasicBlock lbl0 asgns0 jmp0, input0) pgm div = do
    -- just return existing block if we visited this block with given inputs
    -- before
    visitedBlock <- lookupVisitedBlock lbl0 input0
    case visitedBlock of
      Nothing -> do
        -- New label for the block specialized for given input
        lbl <- genLabel lbl0 input0
        -- Add an empty block for this label to prevent loops
        addBlock lbl0 input0 (Left lbl)
        newBlock <- processBlock lbl
        addBlock lbl0 input0 (Right newBlock)
        return newBlock
      Just (Left loopLbl) ->
        -- This is a bit hacky, we detect a loop, and we should just jump to the
        -- label. One way to implement this is to return a block with empty
        -- body:
        return $ BasicBlock undefined [] (Just $ Goto loopLbl)
        -- Since labels of returned blocks are not used, this is fine for now...
      Just (Right blk) ->
        -- We already compiled this block, just return it
        return blk
  where
    processBlock lbl = do
      let (asgns, input) = genAsgns asgns0 input0
      case jmp0 of
        Just (Goto jmpLbl) -> do
          -- generate(or find) specialized block, and compress the transition
          BasicBlock _ asgns' jmp' <- loop (lookupBlock jmpLbl pgm, input) pgm div
          return $ BasicBlock lbl (asgns ++ asgns') jmp'

        Just (If cond l1 l2) ->
          if isExpStatic div cond
            then
              if eval input cond == "true"
                then compressJmp lbl asgns input l1
                else compressJmp lbl asgns input l2
            else do
              let condExp = reduce input cond
              BasicBlock l1_block _ _ <- loop (lookupBlock l1 pgm, input) pgm div
              BasicBlock l2_block _ _ <- loop (lookupBlock l2 pgm, input) pgm div
              return $ BasicBlock lbl asgns (Just $ If condExp l1_block l2_block)

        _ -> return $ BasicBlock lbl asgns jmp0

    compressJmp :: Label -> [Assignment] -> Input -> Label -> State PEState BasicBlock
    compressJmp lbl asgns input jmpLbl = do
      BasicBlock _ asgns' jmp' <- loop (lookupBlock jmpLbl pgm, input) pgm div
      return $ BasicBlock lbl (asgns ++ asgns') jmp'

    genAsgns :: [Assignment] -> Input -> ([Assignment], Input)
    genAsgns [] input = ([], input)
    genAsgns (a : as) input =
      case genAsgn a input of
        Left  a'     -> first (a' :) (genAsgns as input)
        Right input' -> genAsgns as input'

    genAsgn :: Assignment -> Input
               -- we either update the assignment with new residual assignment
               -- code(in case the variable is marked as D in BTA) or update the
               -- environment with evaluated value(in case the variable is
               -- marked as S in BTA)
            -> Either Assignment Input
    genAsgn (Assignment v e) input
      | S <- lookupDivision div v =
        -- evaluate `e`, update environment
        Right (M.insert v (eval input e) input)
      | otherwise =
        -- generate residual code
        Left (Assignment v (reduce input e))

--------------------------------------------------------------------------------

-- FIXME: We need to implement a buch of primops if we want Turing machine
-- interpreter to work.
evalOp :: Op -> [Val] -> Val
evalOp Hd [VList (h : _)] = h
evalOp Tl [VList (_ : t)] = VList t
evalOp Cons [v, VList l]  = VList (v : l)
evalOp Eq   [v1, v2]      = if v1 == v2 then "true" else "false"
evalOp op   args          = error $ "evalOp: Unhandled case: " ++ show op ++ ", " ++ show args

eval :: Input -> Expr -> Val
eval _ (Constant v) = v
eval input (Var v) =
    fromMaybe (error $ "eval: Can't find " ++ v ++ " in input: " ++ show input)
              (M.lookup v input)
eval input (Op op args) = evalOp op $ map (eval input) args

reduce :: Input -> Expr -> Expr
reduce _     v@Constant{}   = v
reduce input (Var v)        = maybe (Var v) Constant $ M.lookup v input
reduce input (Op op es)     =
    if length vs == length es' then Constant $ evalOp op vs else Op op es'
  where
    es' = map (reduce input) es
    vs  = [ v | Constant v <- es' ]

isExpStatic :: Division -> Expr -> Bool
isExpStatic _   Constant{}  = True
isExpStatic div (Var v)     = lookupDivision div v == S
isExpStatic div (Op _ exps) = and $ map (isExpStatic div) exps
