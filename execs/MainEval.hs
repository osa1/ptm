{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}

module Main (main) where

import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Language.Haskell.Exts as HSE
import Safe (readMay)
import System.Console.Haskeline
import System.Directory (doesFileExist)

import CoreLike.Debug (loadState, saveState)
import CoreLike.Eval
import CoreLike.ToHSE

main :: IO ()
main = do
    preludeExists <- doesFileExist "Prelude.hs"
    if preludeExists
       then initState "Prelude.hs" >>= \case
              Left err -> do
                putStrLn $ "Can't parse prelude: " ++ err
                runREPL Nothing
              Right state -> do
                putStrLn "Prelude loaded."
                runREPL (Just state)
       else runREPL Nothing

data REPLCmd
  = Step
  | Drive
  | Eval
  | Load String
  | Term String
  | Repr
  | Residual
  | GC
  | SaveFile FilePath
  | LoadFile FilePath
  deriving (Show, Read, Eq)

runREPL :: Maybe State -> IO ()
runREPL initSt = do
    currentState :: IORef (Maybe State)   <- newIORef initSt
    lastCmd      :: IORef (Maybe REPLCmd) <- newIORef Nothing

    let
      printState :: Bool -> InputT IO ()
      printState s = when s $ do
        cs <- liftIO (readIORef currentState)
        maybe (return ()) (outputStrLn . showState) cs

      runCmd :: Maybe REPLCmd -> InputT IO Bool
      runCmd (Just Step) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> do
            outputStrLn "Can't evaluate, state is not set."
            outputStrLn "Try \"Load\" and \"Term\" commands."
            return False
          Just st ->
            case evalStep st of
              Nothing -> outputStrLn "Can't evaluate further." >> return False
              Just st' -> liftIO (writeIORef currentState (Just st')) >> return True

      runCmd (Just Drive) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> do
            outputStrLn "Can't drive, state is not set."
            outputStrLn "Try \"Load\" and \"Term\" commands."
            return False
          Just st -> liftIO (writeIORef currentState $ Just $ drive st) >> return True

      runCmd (Just Eval) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> do
            outputStrLn "Can't evaluate, state is not set."
            outputStrLn "Try \"Load\" and \"Term\" commands."
            return False
          Just st ->
            case eval st of
              Nothing -> outputStrLn "Can't evaluate further." >> return False
              Just (st', _) -> liftIO (writeIORef currentState $ Just st') >> return True

      runCmd (Just (Load path)) =
        liftIO (initState path) >>= \case
          Left err -> outputStrLn ("Can't parse file: " ++ err) >> return False
          Right st -> liftIO (writeIORef currentState (Just st)) >> return True

      runCmd (Just (Term tm)) = do
        cur <- fromMaybe (undefined, M.empty, []) <$> liftIO (readIORef currentState)
        case setTerm tm cur of
          Left err -> outputStrLn ("Can't parse term: " ++ err) >> return False
          Right st -> liftIO (writeIORef currentState $ Just st) >> return True

      runCmd (Just Repr) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> do
            outputStrLn "State is not set."
            outputStrLn "Try \"Load\" and \"Term\" commands."
            return False
          Just (term, _, _) -> do
            outputStrLn $ show term
            return False

      runCmd (Just GC) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> return False
          Just (term, env, stack) -> do
            liftIO $ writeIORef currentState $ Just (term, gc term env stack, stack)
            return True

      runCmd (Just Residual) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> do
            outputStrLn "Can't residualize: Context is not set."
            return False
          Just state -> do
            outputStrLn (HSE.prettyPrint $ termToHSE $ residualize state)
            return False

      runCmd (Just (LoadFile f)) =
        liftIO (loadState f) >>= \case
          Left err -> do
            outputStrLn ("Can't load from file " ++ f ++ ": " ++ err)
            return False
          Right s  -> liftIO (writeIORef currentState $ Just s) >> return True

      runCmd (Just (SaveFile f)) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> outputStrLn "Can't save to file: Context is not set." >> return False
          Just s  -> liftIO (saveState f s) >> outputStrLn "Done." >> return False

      runCmd Nothing = outputStrLn "Can't parse that." >> return False

    runInputT defaultSettings $ forever $ do
      getInputLine "> " >>= \case
        Just input
          | null input ->
              liftIO (readIORef lastCmd) >>= runCmd >>= printState
          | otherwise  -> do
              let cmd = readMay input
              maybe (return ()) (liftIO . writeIORef lastCmd . Just) cmd
              runCmd cmd >>= printState
        Nothing ->
          liftIO (readIORef lastCmd) >>= runCmd >>= printState
