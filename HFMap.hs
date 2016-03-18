{-# LANGUAGE Rank2Types #-}
module HFMap (HFMap, empty, insert,lookup,singleton, (!), pfmap) where

import KeyM
import Dynamic
import Data.Maybe
import qualified Data.IntMap.Lazy as I
import Prelude hiding (lookup)

data HFMap s f = HFMap (I.IntMap (FDynamic (Key s) f))

empty :: HFMap s f
empty = HFMap (I.empty)

insert :: Key s a -> f a -> HFMap s f -> HFMap s f
insert k v (HFMap m) = HFMap $ I.insert (hashKey k) (toFDynamic k v) m

singleton :: Key s a -> f a -> HFMap s f
singleton k a = insert k a empty

lookup :: Key s a -> HFMap s f -> Maybe (f a)
lookup k (HFMap m) =
    do b <- I.lookup (hashKey k) m
       fromFDynamic k b

(!) :: HFMap s f -> Key s a -> f a
m ! k = fromJust (lookup k m)

pfmap :: (forall x. f x -> g x) -> HFMap s f -> HFMap s g
pfmap f (HFMap m) = HFMap (fmap (fmapf f) m)
