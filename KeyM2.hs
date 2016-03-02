{-# LANGUAGE Rank2Types,GeneralizedNewtypeDeriving, GADTs #-}
module KeyM2 where

import HList
import Control.Monad.State
import Unsafe.Coerce

type Key = HIndex

data KeyIndex l where
  KeyIndex :: HIndex l a -> KeyIndex l

newtype KeyM l a = KeyM (State (KeyIndex l) a)

newKey :: KeyM s (Key s a)
newKey = KeyM $
   do KeyIndex i <- get
      let res = unsafeCoerce $ HTail i
      put (KeyIndex res)
      return res

runKeyM :: (forall s. KeyM s a) -> a
runKeyM (KeyM m) = evalState m (KeyIndex HHead)
