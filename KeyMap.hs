{-# LANGUAGE GADTs #-}
module KeyMap(Box(..), unlock, KeyMap, singleton, empty, insert,lookup, (!)) where

import KeyM
import Control.Monad
import Prelude hiding (lookup,(!))
import Data.Maybe

data Box s where
  Lock :: Key s a -> a -> Box s

unlock :: Key s a -> Box s -> Maybe a
unlock k (Lock k' x) =
   case testEquality k k' of
    Just Refl  -> Just x
    Nothing    -> Nothing


newtype KeyMap s = Km [Box s]

empty :: KeyMap s
empty = Km []

insert :: Key s a -> a -> KeyMap s -> KeyMap s
insert k v (Km l) = Km (Lock k v : l)	

singleton k v = insert k v empty

lookup :: Key s a -> KeyMap s -> Maybe a
lookup k (Km [])       = Nothing
lookup k (Km (h : t))  = 
  unlock k h `mplus` lookup k (Km t)

(!) :: KeyMap s -> Key s a -> a
m ! k = fromJust (lookup k m)
