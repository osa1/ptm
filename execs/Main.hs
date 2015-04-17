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
  , fConfig    :: Config
  }

data Config = Config
  { cEnv    :: Env
  , cRestrs :: [Restriction]
    -- swap these two |
  , cSteps  :: IM.IntMap Config
  , cTerm   :: Term
  }

gotoToplevel :: Focus -> Focus
gotoToplevel f@(Focus _ Nothing  _) = f
gotoToplevel   (Focus _ (Just f) _) = gotoToplevel f

initToplevel :: Term -> Env -> Focus
initToplevel term env = Focus 0 Nothing (Config env [] IM.empty term)

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
              liftIO $ readIORef focus >>= \case
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
              case step env term of
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

        Just notSupported -> outputStrLn $ "Command not implemented yet: " ++ show notSupported
        Nothing -> outputStrLn "Can't parse that."

printFocus :: MonadIO m => Maybe Focus -> InputT m ()
printFocus Nothing = do
    outputStrLn "Nothing in focus."
    outputStrLn "Load an environment using Load command."
    outputStrLn "Set focused term using Term command."
printFocus (Just (Focus lvl _ c)) = do
    outputStrLn $ "Current level: " ++ show lvl
    outputStrLn $ pprintConfigSteps c

pprintConfigSteps :: Config -> String
pprintConfigSteps c = unlines $ iter 0 c
  where
    iter :: Int -> Config -> [String]
    iter num (Config _env _restrs steps term) =
      let (f : r)   = lines $ HSE.prettyPrint $ termToHSE term
          lnLen     = (length $ show $ IM.size steps) + 2
          numStr    = show num
          pfxdLines = ((replicate (lnLen - length numStr - 2) ' ' ++ numStr ++ ". " ++ f) : r)
          stepLines = concatMap (map ("  " ++) . uncurry iter) $ IM.toList steps
       in pfxdLines ++ stepLines
