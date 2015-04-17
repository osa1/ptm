{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}

module Main where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.IORef
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Language.Haskell.Exts as HSE
import Safe (readMay)
import System.Console.Haskeline
import System.Environment
import qualified Text.PrettyPrint.Leijen as PP

import CoreLike.Parser
import CoreLike.Simplify
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
  | Move Int
  | Up
  | TopLevel
  | ShowEnv -- TODO: maybe only shows used used parts
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
  , fStepNum   :: Int
  , fPrevFocus :: Maybe Focus -- Nothing if root
  , fConfig    :: Config
  }

data Config = Config
  { cEnv    :: Env
  , cRestrs :: [Restriction]
    -- swap these two |
  , cSteps  :: IM.IntMap Config
  , cTerm   :: Term
  }

goTop :: Focus -> Focus
goTop f@(Focus _ _ Nothing  _) = f
goTop   (Focus _ i (Just f@(Focus _ _ _ cUp)) c) =
    f{fConfig = cUp{cSteps = IM.insert i c (cSteps cUp)}}


gotoToplevel :: Focus -> Focus
gotoToplevel f@(Focus _ _ Nothing  _) = f
gotoToplevel f@(Focus _ _ Just{} _)   = gotoToplevel (goTop f)

initToplevel :: Term -> Env -> Focus
initToplevel term env = Focus 0 0 Nothing (Config env [] IM.empty term)

runREPL :: IO ()
runREPL = do
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
              liftIO (readIORef focus) >>= \case
                Nothing ->
                  liftIO $ writeIORef focus (Just $ initToplevel tm' M.empty)
                Just f -> do
                  let f' = gotoToplevel f
                  -- FIXME: get toplevel env here
                  liftIO $ writeIORef focus (Just $ initToplevel tm' (cEnv $ fConfig f'))

        -- FIXME: Driver should take restrictions into account...
        Just Step -> do
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "What am I supposed to drive? (set a term using `term` command)"
            Just f  -> do
              let Config env restrs _steps term = fConfig f
              case fmap simpl $ step env term of
                Transient term' ->
                  -- Should I really update an old state here? When is this old
                  -- state not empty?
                  liftIO $ writeIORef focus $
                    Just f{fConfig=Config env restrs
                            (IM.singleton 0 (Config env restrs IM.empty term')) term}
                Split terms     -> do
                  -- FIXME: Env should be updated in lets and cases
                  let steps =
                        IM.fromList $ zip [0..] $
                          map (\(restrs', term') -> Config env restrs' IM.empty term') terms
                  liftIO $ writeIORef focus $
                    Just f{fConfig=Config env restrs steps term}
                Stuck           ->
                  outputStrLn "Can't take any steps..."

        Just (Load path) ->
          liftIO (parseFile path) >>= \case
            Left err -> outputStrLn err
            Right env ->
              liftIO $ writeIORef focus $ Just $ initToplevel (Value $ Data "()" []) (M.fromList env)

        Just (Move i) ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't move focus, context is not set."
            Just f@(Focus curLvl _ _ (Config _ _ steps _)) ->
              case IM.lookup i steps of
                Nothing -> outputStrLn "Can't move focus: No such context."
                Just conf ->
                  liftIO $ writeIORef focus $ Just $ Focus (curLvl + 1) i (Just f) conf

        Just Up ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't move focus, context is not set."
            Just f -> liftIO $ writeIORef focus $ Just $ goTop f

        Just TopLevel ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't move focus, context is not set."
            Just f  ->
              liftIO $ writeIORef focus $ Just $ gotoToplevel f

        Just ShowEnv ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't show environment, context is not set."
            Just f  -> do
              let env     = cEnv $ fConfig f
                  -- term    = cTerm $ fConfig f
                  -- fvs     = fvsTerm term
                  -- usedEnv = M.filterWithKey (\k _ -> k `S.member` fvs) env
              outputStrLn $ pprintEnv env

        Just notSupported -> outputStrLn $ "Command not implemented yet: " ++ show notSupported
        Nothing -> outputStrLn "Can't parse that."

printFocus :: MonadIO m => Maybe Focus -> InputT m ()
printFocus Nothing = do
    outputStrLn "Nothing in focus."
    outputStrLn "Load an environment using Load command."
    outputStrLn "Set focused term using Term command."
printFocus (Just (Focus lvl _ _ c)) = do
    outputStrLn $ "Current level: " ++ show lvl
    outputStrLn $ pprintConfigSteps c

pprintConfigSteps :: Config -> String
pprintConfigSteps c = unlines $ iter 0 c
  where
    iter :: Int -> Config -> [String]
    iter num (Config _env _restrs steps term) =
      let (f : r)   = lines $ HSE.prettyPrint $ termToHSE term
          lnLen     = length $ show $ abs $ IM.size steps - 1
          numStr    = show num
          pfxdLines = ((replicate (lnLen - length numStr) ' ' ++ numStr ++ ". " ++ f) :
                       (map (replicate (lnLen + 2) ' ' ++) r))
          stepLines = concatMap (map ("  " ++) . uncurry iter) $ IM.toList steps
       in pfxdLines ++ stepLines
