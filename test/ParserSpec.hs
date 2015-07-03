module ParserSpec where

import Control.Monad
import qualified Language.Haskell.Exts as HSE
import System.Directory
import System.FilePath

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit hiding (path)
-- I hate it when libraries export unqualified record field selectors with super
-- generic names, like path, ret, result, etc.

import CoreLike.Parser
import CoreLike.ToHSE

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    files <- runIO $ loadTestFiles "tests"
    describe "parsing and printing" $ forM_ files $ \(path, contents) ->
      fromHUnitTest $ TestLabel ("parsing and printing " ++ path) $ TestCase $
        case parse contents of
          Left err -> assertFailure $ "Parsing failed: " ++ err
          Right bs ->
            let printed = HSE.prettyPrint $ hseModule bs in
            case parse printed of
              Left err -> assertFailure $ unlines
                [ "Can't parse printed module:", printed, "error:", err ]
              Right bs' ->
                assertEqual
                  ("Printed module is parsed differently\nprinted:\n" ++ printed)
                  bs bs'

loadTestFiles :: FilePath -> IO [(FilePath, String)]
loadTestFiles root = getDirectoryContents root >>= fmap concat . mapM (\f -> do
  let p = root </> f
  isDir <- doesDirectoryExist p
  if | head f == '.' -> return []
     | isDir -> loadTestFiles p
     | otherwise -> ((:[]) . (p,)) `fmap` readFile p)
