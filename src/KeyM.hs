{-# LANGUAGE Rank2Types,GeneralizedNewtypeDeriving #-}
module KeyM(module Data.Type.Equality, KeyM, Key, newKey, runKeyM) where

import Unsafe.Coerce
import Data.Type.Equality
import Control.Applicative
import Control.Monad

data TreePath = Start | Leftc TreePath | Rightc TreePath deriving (Eq)

type Name = TreePath
type NameSupply = TreePath

newNameSupply :: NameSupply
newNameSupply = Start

split :: NameSupply -> (NameSupply, NameSupply)
split s = (Leftc s, Rightc s)

supplyName :: NameSupply -> Name
supplyName = id

instance TestEquality (Key s) where
  testEquality (Key i) (Key j)
    | i == j     = Just (unsafeCoerce Refl)
    | otherwise  = Nothing


data KeyM s a = KeyM { getKeyM :: NameSupply -> a }
data Key s a = Key Name


newKey :: KeyM s (Key s a)
newKey = KeyM $ \s -> Key (supplyName s)

instance Functor (KeyM s) where
  fmap = liftM

instance Applicative (KeyM s) where
  pure = return
  (<*>) = ap

instance Monad (KeyM s) where
  return x = KeyM $ \_ -> x
  m >>= f = KeyM $ \s ->
     let (sl,sr) = split s
     in getKeyM (f (getKeyM m sl)) sr

runKeyM :: (forall s. KeyM s a) -> a
runKeyM (KeyM f) = f newNameSupply
