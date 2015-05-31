-- | Utilities to help debugging and testing.
module CoreLike.Debug where

import Data.Binary (decodeFileOrFail, encodeFile)

import CoreLike.Eval

saveState :: FilePath -> State -> IO ()
saveState = encodeFile

loadState :: FilePath -> IO (Either String State)
loadState f = do
    ret <- decodeFileOrFail f
    return $ case ret of
               Left (_, err) -> Left err
               Right s -> Right s

loadState' :: FilePath -> IO State
loadState' = fmap (\(Right r) -> r) . loadState
