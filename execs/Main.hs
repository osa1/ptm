{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}

module Main where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.IORef
import qualified Data.Map as M
import qualified Language.Haskell.Exts as HSE
import Safe
import System.Console.Haskeline
import System.Environment
import qualified Text.PrettyPrint.Leijen as PP

import CoreLike.Parser
import CoreLike.Step
import CoreLike.Syntax
import CoreLike.ToHSE

main :: IO ()
main = do
    runREPL
    -- (a : _) <- getArgs
    -- parseFile a >>= \case
    --   Left err -> error err
    --   Right st -> do
    --     print st
    --     putStrLn "\nHSE conversion and printer: ----------------"
    --     putStrLn $ HSE.prettyPrint (hseModule st)

data REPLCmd
  = Step
  | MoveFocus Int
  | TopLevel
  | Load FilePath
  | History
  | Term String
  | MkSession FilePath
  | Save FilePath
  deriving (Show, Eq, Read)
  -- using Read instance for parsing for now

newtype Level = Level (IM.IntMap (Env, Term, Maybe Level))

-- Could this be implemented as a zipper for more efficiency?
-- (or is this already a zipper?)
data Focus = Focus
  { fCurLvl    :: Int
  , fPrevFocus :: Maybe Focus -- Nothing if root
  , fTerm      :: Term
  , fEnv       :: Env
  , fRestrs    :: [Restriction]
  , fSteps     :: IM.IntMap (Env, [Restriction], Term)
  }

initToplevel :: Term -> Env -> Focus
initToplevel term env = Focus 0 Nothing term env [] IM.empty

runREPL :: IO ()
runREPL = do
    -- TODO: Do I need a state transformer?
    focus :: IORef (Maybe Focus) <- newIORef Nothing

    runInputT defaultSettings $ forever $ do
      printFocus =<< liftIO (readIORef focus)

      input <- getInputLine "> "
      case input >>= readMay of

        Just (Term tm) -> do
          outputStrLn "Parsing the term."
          case parseTerm tm of
            Left err -> outputStrLn err
            Right tm' -> do
              outputStrLn "Term parsed:"
              outputStrLn (HSE.prettyPrint $ termToHSE tm')
              f <- liftIO $ readIORef focus
              case f of
                Nothing ->
                  liftIO $ writeIORef focus (Just $ initToplevel tm' M.empty)
                Just Focus{fEnv=env} ->
                  -- FIXME: get toplevel env here
                  liftIO $ writeIORef focus (Just $ initToplevel tm' env)

        -- FIXME: Driver should take restrictions into account...
        Just Step -> do
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "What am I supposed to drive? (set a term using `term` command)"
            Just f@Focus{fTerm=term, fEnv=env, fSteps=steps} -> do
              case step env term of
                Transient term' ->
                  -- Should I really update an old state here? When is this old
                  -- state not empty?
                  liftIO $ writeIORef focus $
                    Just f{fSteps=IM.insert 0 (env, fRestrs f, term') steps}
                Split terms     ->
                  liftIO $ writeIORef focus $
                    Just f{fSteps=IM.fromList $ zip [0..] $
                                    map (\(restrs, term') -> (env, restrs, term')) terms}
                Stuck           ->
                  outputStrLn "Can't take any steps..."

        Just (Load path) ->
          liftIO (parseFile path) >>= \case
            Left err -> outputStrLn err
            Right env ->
              liftIO $ writeIORef focus $ Just $ initToplevel (Value $ Data "()" []) (M.fromList env)

        Just notSupported -> outputStrLn $ "Command not implemented yet: " ++ show notSupported
        Nothing -> outputStrLn "Can't parse that."

printFocus :: MonadIO m => Maybe Focus -> InputT m ()
printFocus Nothing = do
    outputStrLn "Nothing in focus."
    outputStrLn "Load an environment using Load command."
    outputStrLn "Set focused term using Term command."
printFocus (Just f) = do
    outputStrLn $ "Current level: " ++ show (fCurLvl f)
    outputStrLn "Term:"
    outputStrLn $ HSE.prettyPrint $ termToHSE (fTerm f)
    forM_ (IM.toList $ fSteps f) $ \(i, (_, _, t)) ->
      outputStrLn $
        ($ "") . PP.displayS . PP.renderPretty 1 10000 . PP.indent 2 . PP.string . HSE.prettyPrint . termToHSE $ t
