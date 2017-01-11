{-# LANGUAGE Rank2Types,GeneralizedNewtypeDeriving #-}
module KeyMEfficient where

import Data.IORef
import Unsafe.Coerce
import Data.Type.Equality
import Control.Applicative
import Control.Monad
import System.IO.Unsafe
import Control.Monad.Reader
import Control.Monad.ST.Unsafe

newtype KeyM s a = KeyM { getKeyM :: IORef Integer -> a } deriving (Functor, Applicative, Monad)
newtype Key s a = Key Integer

instance TestEquality (Key s) where
  testEquality (Key i) (Key j)
    | i == j     = Just (unsafeCoerce Refl)
    | otherwise  = Nothing

newKey :: KeyM s (Key s a)
newKey = KeyM $ \r -> unsafePerformIO $
  do n <- readIORef r
     writeIORef r (n + 1)
     return (Key n)

runKeyM :: (forall s. KeyM s a) -> a
runKeyM (KeyM f) = f (unsafePerformIO $ newIORef 0)
