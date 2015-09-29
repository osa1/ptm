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
import CoreLike.Utils

import TestUtils

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    files <- runIO $ loadTestFiles "tests"
    describe "parsing and printing" $ forM_ files $ \(path, contents) ->
      fromHUnitTest $ TestLabel ("parsing and printing " ++ path) $ TestCase $
        case parseModule contents of
          Left err -> assertFailure $ "Parsing failed: " ++ err
          Right bs ->
            let printed = HSE.prettyPrint $ hseModule bs in
            case parseModule printed of
              Left err -> assertFailure $ unlines
                [ "Can't parse printed module:", printed,
                  "printed AST:", showPretty bs,
                  "error:", err ]
              Right bs' ->
                assertEqStrs
                  (unlines [ "Printed module is parsed differently",
                             "printed:", printed ])
                  bs bs'
                  (showPretty bs) (showPretty bs')

loadTestFiles :: FilePath -> IO [(FilePath, String)]
loadTestFiles root = getDirectoryContents root >>= fmap concat . mapM f
  where
    f path
      | ('.' : _) <- path
      = return []
      | otherwise
      = do let p = root </> path
           isDir <- doesDirectoryExist p
           if isDir then loadTestFiles p
                    else ((:[]) . (p,)) `fmap` readFile p
