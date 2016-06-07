
module KeyMap(KeyMap, singleton, empty, insert,lookup, (!)) where

import KeyM
import Control.Monad
import Box
import Prelude hiding (lookup,(!))
import Data.Maybe

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
