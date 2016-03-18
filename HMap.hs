
module HMap(HMap, empty, insert,lookup,singleton, (!)) where

import KeyM
import Dynamic
import qualified Data.IntMap.Lazy as I
import Prelude hiding (lookup)
import Data.Maybe

data HMap s = HMap (I.IntMap (Dynamic (Key s)))

empty :: HMap s
empty = HMap (I.empty)

insert :: Key s a -> a -> HMap s -> HMap s
insert k v (HMap m) = HMap $ I.insert (hashKey k) (toDynamic k v) m

singleton :: Key s a -> a -> HMap s
singleton k a = insert k a empty

lookup :: Key s a -> HMap s -> Maybe a
lookup k (HMap m) =
    do b <- I.lookup (hashKey k) m
       fromDynamic k b

(!) :: HMap s ->  Key s a -> a
m ! k = fromJust $ lookup k m
