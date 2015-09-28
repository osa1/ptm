module CoreLike.Utils where

import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Pretty

showPretty :: Show a => a -> String
showPretty a =
    let s = show a in
    case parseExp s of
      ParseOk x     -> prettyPrint x
      ParseFailed{} -> s
