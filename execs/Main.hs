module Main where

import System.Environment

import CoreLike.Parser

main :: IO ()
main = do
    (a : _) <- getArgs
    print =<< parseFile a
