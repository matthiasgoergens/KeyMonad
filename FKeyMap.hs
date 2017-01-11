{-# LANGUAGE GADTs #-}
module FKeyMap(FBox(..), funlock, FKeyMap, singleton, empty, insert,lookup, (!)) where

import KeyM
import Control.Monad
import Prelude hiding (lookup,(!))
import Data.Maybe
import PFunctor

data FBox s f where
  FLock :: Key s a -> f a -> FBox s f

funlock :: Key s a -> FBox s f -> Maybe (f a)
funlock k (FLock k' x) =
  case testEquality k k' of
    Just Refl  -> Just x
    Nothing    -> Nothing

instance PFunctor (FBox s) where
  pfmap f (FLock k x) = FLock k (f x)

newtype FKeyMap s f = FKm [FBox s f]

empty :: FKeyMap s f
empty = FKm []

singleton :: Key s a -> f a -> FKeyMap s f
singleton k v = insert k v empty

insert :: Key s a -> f a -> FKeyMap s f  -> FKeyMap s f
insert k v (FKm l) = FKm (FLock k v : l)

lookup :: Key s a -> FKeyMap s f -> Maybe (f a)
lookup k (FKm [])       = Nothing
lookup k (FKm (h : t))  =
  funlock k h `mplus` lookup k (FKm t)

(!) :: FKeyMap s f -> Key s a -> f a
m ! k = fromJust (lookup k m)

instance PFunctor (FKeyMap s) where
  pfmap f (FKm l) = FKm $ map (pfmap f) l

