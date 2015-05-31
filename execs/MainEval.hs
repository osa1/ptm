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
  | Simpl
  | SaveFile FilePath
  | LoadFile FilePath
  | Tee FilePath REPLCmd
  deriving (Show, Read, Eq)

runREPL :: Maybe State -> IO ()
runREPL initSt = do
    currentState :: IORef (Maybe State)    <- newIORef initSt
    lastCmd      :: IORef (Maybe REPLCmd)  <- newIORef Nothing
    tee          :: IORef (Maybe FilePath) <- newIORef Nothing

    let
      printState :: Bool -> InputT IO ()
      printState s = when s $
        liftIO (readIORef currentState) >>= \case
          Nothing -> return ()
          Just st -> do
            let sts = showState st
            maybe (return ()) (\f -> liftIO $ writeFile f sts >> writeIORef tee Nothing)
              =<< liftIO (readIORef tee)
            outputStrLn sts

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

      runCmd (Just Simpl) =
        liftIO (readIORef currentState) >>= \case
          Nothing -> return False
          Just (term, env, stack) -> do
            liftIO $ writeIORef currentState $ Just (term, simplHeap env, stack)
            return True

      runCmd (Just Residual) = do
        liftIO (readIORef currentState) >>= \case
          Nothing -> do
            outputStrLn "Can't residualize: Context is not set."
          Just state -> do
            let str = HSE.prettyPrint $ termToHSE $ residualize state
            maybe (return ()) (\f -> liftIO $ writeFile f str >> writeIORef tee Nothing)
              =<< liftIO (readIORef tee)
            outputStrLn str
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

      runCmd (Just (Tee file cmd)) =
        liftIO (writeIORef tee $ Just file) >> runCmd (Just cmd)

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
