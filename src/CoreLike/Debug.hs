-- | Utilities to help debugging and testing.
module CoreLike.Debug where

import Data.Bifunctor (bimap)
import Data.Binary (decodeFileOrFail, encodeFile)

import CoreLike.Eval

saveState :: FilePath -> State -> IO ()
saveState = encodeFile

loadState :: FilePath -> IO (Either String State)
loadState f = bimap snd id <$> decodeFileOrFail f

loadState' :: FilePath -> IO State
loadState' = fmap (\(Right r) -> r) . loadState
