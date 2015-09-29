module ParserSpec where

import Control.Monad
import qualified Language.Haskell.Exts as HSE
import System.Directory
import System.FilePath

import Prelude hiding (print)

import Test.Hspec
import Test.Hspec.Contrib.HUnit
import Test.HUnit hiding (path)

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
        ppp contents parseModule (HSE.prettyPrint . hseModule)

-- | A parse-print-parse assertion.
ppp :: (Show a, Eq a)
    => String                      -- ^ string to ppp
    -> (String -> Either String a) -- ^ parser
    -> (a -> String)               -- ^ printer
    -> Assertion
ppp s parse print = do
    case parse s of
      Left err -> assertFailure $ "Parsing failed: " ++ err
      Right a  ->
        let printed = print a in
        case parse printed of
          Left err -> assertFailure $ unlines
            [ "Can't parse printed module:", printed,
              "printed AST:", showPretty printed,
              "error:", err ]
          Right a' ->
            assertEqStrs
              (unlines [ "Printed module is parsed differently",
                         "printed:", printed ])
              a a'
              (showPretty a) (showPretty a')

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
