{-# LANGUAGE CPP #-}

module Main where

-- Can't nest a `executable` section in Cabal file to a `if ...`, so I'm using
-- CPP to prevent this module to be built without --ghcjs.

-- We can't use __GHCJS__ macro, because it's also defined when -native-too is
-- used by GHCJS.

#ifndef ghcjs_HOST_OS

main :: IO ()
main = return ()

#else

import Data.Bifunctor
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Trans (lift)
import GHCJS.DOM
import GHCJS.DOM.Element
import GHCJS.Foreign
import GHCJS.Types

import qualified Deforestation.Deforest as D
import qualified Deforestation.Parser as D
import qualified Deforestation.ToHSE as D

foreign import javascript unsafe
  "editors[$1][0].getValue()"
  getEditorText :: Int -> IO JSString

foreign import javascript unsafe
  "editors[$1][0].setValue($2)"
  setEditorText :: Int -> JSString -> IO ()

foreign import javascript unsafe
  "editors[$1][1]"
  getEditorButton :: Int -> IO Element

foreign import javascript unsafe "$r = NUM_EDITORS" numEditors :: IO Int

deforestForm :: Int -> IO (String, String)
deforestForm i = do
    contents <- fromJSString <$> getEditorText i
    let (decls, pgm) =
          uncurry D.simplDefs $ D.deforest' $ D.parseTerm' contents
        strs = ( unlines . map D.ppFn . M.toList $ D.gc decls pgm
               , D.ppTTerm pgm )
    return strs

main :: IO ()
main = do
    editors <- numEditors
    print editors
    forM_ [0 .. editors-1] $ \i -> do
      button <- getEditorButton i
      elementOnclick button $ do
        -- t <- lift $ getEditorText i
        -- lift (putStrLn . fromJSString $ t)
        (str1, str2) <- lift $ deforestForm i
        lift $ setEditorText i (toJSString $ str1 ++ "\n\nmain = " ++ str2)

#endif
