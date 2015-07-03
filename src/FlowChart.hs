module FlowChart where

import FlowChart.Division (Division (..), congruentDivision, initDivision)
import FlowChart.Lexer (tokenize)
import FlowChart.Mix
import FlowChart.Parser (program)
import FlowChart.Printer
import FlowChart.Syntax

import Data.List (partition)
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding (div)
import Text.Parsec (parse)

parseFile' :: FilePath -> IO Program
parseFile' path = do
    contents <- readFile path
    either (error . show) return $ tokenize path contents >>= parse program path

dividePgm :: [Var] -> [Var] -> Program -> Division
dividePgm (S.fromList -> ss) (S.fromList -> ds) pgm =
    congruentDivision (initDivision (Division ss ds) pgm) pgm

pePgm :: FilePath -> Input -> IO (Program, Label)
pePgm path input = do
    pgm <- parseFile' path
    let div = dividePgm (M.keys input) [] pgm
    putStrLn $ "division: " ++ show div
    return $ mix pgm div input

test1 :: IO ()
test1 = do
    (Program rd bs, entry) <- pePgm "programs/FlowChart/Lookup.L"
      (M.fromList [("Namelist", VList ["a", "b", "c"]), ("Name", "c")])

    -- move entry block to first position
    let ([entryBlock], rest) = partition (\(BasicBlock lbl _ _) -> lbl == entry) bs
    putStrLn $ pprintPgm (Program rd (entryBlock : rest))

test2 :: IO ()
test2 = do
    (Program rd bs, entry) <- pePgm "programs/FlowChart/Lookup.L" M.empty

    -- move entry block to first position
    let ([entryBlock], rest) = partition (\(BasicBlock lbl _ _) -> lbl == entry) bs
    putStrLn $ pprintPgm (Program rd (entryBlock : rest))

-- This fails with an error, because we don't handle base cases and make some
-- assumptions like Namelist always include Name and lists are infinite etc.
--
-- Handling errors in mix is possible, but I won't bother for this exercise.
test3 :: IO ()
test3 = do
    (Program rd bs, entry) <- pePgm "programs/FlowChart/Lookup.L"
      (M.fromList [("Valuelist", VList ["a", "b"])])

    -- move entry block to first position
    let ([entryBlock], rest) = partition (\(BasicBlock lbl _ _) -> lbl == entry) bs
    putStrLn $ pprintPgm (Program rd (entryBlock : rest))
