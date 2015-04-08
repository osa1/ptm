{-# LANGUAGE LambdaCase #-}

module Main where

import qualified Language.Haskell.Exts as HSE
import System.Environment

import CoreLike.Parser
import CoreLike.ToHSE

main :: IO ()
main = do
    (a : _) <- getArgs
    parseFile a >>= \case
      Left err -> error err
      Right st -> do
        print st
        putStrLn "\nHSE conversion and printer: ----------------"
        putStrLn $ HSE.prettyPrint (hseModule st)
