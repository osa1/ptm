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
import qualified Text.PrettyPrint.Leijen as PP

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
  | Load String
  | Term String
  deriving (Show, Read, Eq)

runREPL :: Maybe State -> IO ()
runREPL initSt = do
    currentState :: IORef (Maybe State)   <- newIORef initSt
    stateHistory :: IORef [State]         <- newIORef []
    lastCmd      :: IORef (Maybe REPLCmd) <- newIORef Nothing

    let
      runCmd (Just Step) = do
        liftIO (readIORef currentState) >>= \case
          Nothing -> do
            outputStrLn "Can't evaluate, state is not set."
            outputStrLn "Try \"Load\" and \"Term\" commands."
          Just st ->
            case evalStep st of
              Nothing -> outputStrLn "Can't evaluate further."
              Just st' -> liftIO $ do
                writeIORef currentState (Just st')
                modifyIORef stateHistory (st :)

      runCmd (Just (Load path)) =
        liftIO (initState path) >>= \case
          Left err -> outputStrLn $ "Can't parse file: " ++ err
          Right st -> liftIO (writeIORef currentState (Just st))

      runCmd (Just (Term tm)) = do
        cur <- fromMaybe (undefined, M.empty, []) <$> liftIO (readIORef currentState)
        case setTerm tm cur of
          Left err -> outputStrLn $ "Can't parse term: " ++ err
          Right st -> liftIO (writeIORef currentState $ Just st)

      runCmd Nothing = outputStrLn "Can't parse that."

    runInputT defaultSettings $ forever $ do
      cs <- liftIO (readIORef currentState)
      -- FIXME: We should print the whole state instead.
      maybe (return ()) (outputStrLn . pprintState) cs
      getInputLine "> " >>= \case
        Just input
          | null input -> liftIO (readIORef lastCmd) >>= runCmd
          | otherwise   -> do
              let cmd = readMay input
              maybe (return ()) (liftIO . writeIORef lastCmd . Just) cmd
              runCmd cmd
        Nothing -> liftIO (readIORef lastCmd) >>= runCmd

pprintTerm :: State -> String
pprintTerm (term, _, _) = HSE.prettyPrint $ termToHSE term

pprintStack :: State -> String
pprintStack (_, _, stack) =
    PP.displayS (PP.renderPretty 0.8 100 $ PP.list (map (PP.text . show) stack)) ""

pprintState :: State -> String
pprintState (term, env, stack) = flip PP.displayS "" . PP.renderPretty 0.8 100 . PP.tupled $
    [ PP.list $ map (\(k, v) -> PP.nest 4 (PP.text k PP.<+> PP.text "=" PP.</>
                                             PP.string (HSE.prettyPrint (termToHSE v))))
                    (M.toList env)
    , PP.list $ map (PP.text . show) stack
    , PP.string (HSE.prettyPrint $ termToHSE term)
    ]
