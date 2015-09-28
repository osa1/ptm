module CoreLike.TagBag where

import Control.Monad.State
import Data.Foldable (toList)
import qualified Data.Set as S

import CoreLike.Syntax

type Tag = Int
type TagBag = [Tag]

type TaggedTerm = Term Tag
type TaggedValue = Value Tag

tagTerm :: Term ann -> TaggedTerm
tagTerm tm = evalState (traverse (const freshTag) tm) 1
  where
    freshTag = do t <- get; put (t + 1); return t

tagBag :: TaggedTerm -> [Tag]
tagBag = toList

(<|) :: TagBag -> TagBag -> Bool
(<|) ts1 ts2 = S.fromList ts1 == S.fromList ts2 && length ts1 /= length ts2
