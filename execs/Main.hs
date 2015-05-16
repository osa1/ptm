{-# LANGUAGE LambdaCase, NondecreasingIndentation, ScopedTypeVariables #-}

module Main where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.IORef
import qualified Data.Map as M
import qualified Language.Haskell.Exts as HSE
import Safe (readMay)
import System.Console.Haskeline
import System.Directory (doesFileExist)

import CoreLike.Parser
import CoreLike.Simplify
import CoreLike.Step hiding (step)
import qualified CoreLike.Step as S
import CoreLike.Syntax
import CoreLike.ToHSE

main :: IO ()
main = do
    preludeExists <- doesFileExist "Prelude.hs"
    runREPL $ if preludeExists then Just "Prelude.hs" else Nothing

data REPLCmd
  = Step
  | Steps Int
  | Move Int
  | Up
  | Down
  | TopLevel
  | Bottom
  | ShowEnv -- TODO: maybe only shows used used parts
  | Load FilePath
  | History
  | Term String
  | MkSession FilePath
  | Save FilePath
  -- Debugging stuff
  | Repr -- ^ Print internal representation of the focused term
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

goUp :: Focus -> Focus
goUp f@(Focus _ _ Nothing  _) = f
goUp   (Focus _ i (Just f@(Focus _ _ _ cUp)) c) =
    f{fConfig = cUp{cSteps = IM.insert i c (cSteps cUp)}}

goDown :: Focus -> Focus
goDown f@(Focus curLvl _ _ (Config _ _ steps _))
  | IM.size steps /= 1 = f
  | otherwise          =
      Focus (curLvl + 1) 0 (Just f) (snd . head $ IM.toList steps)

gotoToplevel :: Focus -> Focus
gotoToplevel f@(Focus _ _ Nothing  _) = f
gotoToplevel f@(Focus _ _ Just{} _)   = gotoToplevel (goUp f)

gotoBottom :: Focus -> Focus
gotoBottom f@(Focus curLvl _ _ (Config _ _ steps _)) =
    case IM.toList steps of
      [(_, c)] -> gotoBottom (Focus (curLvl + 1) 0 (Just f) c)
      _        -> f

initToplevel :: Term -> Env -> Focus
initToplevel term env = Focus 0 0 Nothing (Config env [] IM.empty term)

runREPL :: Maybe String -> IO ()
runREPL prelude = do
    focus :: IORef (Maybe Focus) <- newIORef Nothing

    runInputT defaultSettings $ do

      let load path = do
            liftIO (parseFile path) >>= \case
              Left err -> outputStrLn err
              Right env ->
                liftIO $ writeIORef focus $
                  Just $ initToplevel (Value $ Data "()" []) (M.fromList env)

      maybe (return ()) load prelude

      forever $ do
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
              case fmap simpl $ S.step env term of
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

        Just (Steps n) -> do
          liftIO (readIORef focus) >>= \case
            Nothing ->
              outputStrLn "What am I supposed to drive? (set a term using `term` command)"
            Just f  ->
              liftIO $ writeIORef focus $ Just f{fConfig=step (fConfig f) n}

        Just (Load path) -> load path

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
            Just f -> liftIO $ writeIORef focus $ Just $ goUp f

        Just Down ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't move focus, context is not set."
            Just f -> liftIO $ writeIORef focus $ Just $ goDown f

        Just TopLevel ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't move focus, context is not set."
            Just f  ->
              liftIO $ writeIORef focus $ Just $ gotoToplevel f

        Just Bottom ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't move focus, context is not set."
            Just f ->
              liftIO $ writeIORef focus $ Just $ gotoBottom f

        Just ShowEnv ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't show environment, context is not set."
            Just f  -> do
              let env     = cEnv $ fConfig f
                  -- term    = cTerm $ fConfig f
                  -- fvs     = fvsTerm term
                  -- usedEnv = M.filterWithKey (\k _ -> k `S.member` fvs) env
              outputStrLn $ pprintEnv env

        Just Repr ->
          liftIO (readIORef focus) >>= \case
            Nothing -> outputStrLn "Can't show repr, context is not set."
            Just f -> outputStrLn . show . cTerm . fConfig $ f

        Just notSupported -> outputStrLn $ "Command not implemented yet: " ++ show notSupported
        Nothing -> outputStrLn "Can't parse that."

step :: Config -> Int -> Config
step c 0 = c
step c@(Config env restrs _steps term) n =
    case fmap simpl $ S.step env term of
      Transient term' ->
        Config env restrs
          (IM.singleton 0 (step (Config env restrs IM.empty term') (n - 1))) term
      Split terms ->
        let steps =
              IM.fromList $ zip [0..] $
                map (\(restrs', term') -> step (Config env restrs' IM.empty term') (n - 1))
                    terms
        in Config env restrs steps term
      Stuck -> c

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
