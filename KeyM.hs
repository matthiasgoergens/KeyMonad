{-# LANGUAGE Rank2Types,GeneralizedNewtypeDeriving #-}


module KeyM(module Data.Type.Equality, KeyM, Key, newKey, hashKey, runKeyM) where

import Control.Monad.State
import Control.Monad.Fix
import Control.Applicative
import Unsafe.Coerce
import Data.Type.Equality

newtype KeyM  s a = KeyM (State Integer a) deriving (MonadFix, Monad,Applicative, Functor)
newtype Key   s a = Key Integer


newKey :: KeyM s (Key s a)
newKey = KeyM $ do i <- get ; put (i + 1) ; return (Key i)

hashKey :: Key s a -> Int
hashKey (Key k) = fromIntegral k

instance TestEquality (Key l) where
  testEquality (Key i) (Key j)
    | i == j     = Just (unsafeCoerce Refl)
    | otherwise  = Nothing

runKeyM :: (forall s . KeyM s a) -> a
runKeyM (KeyM m) = fst $ runState m 0
