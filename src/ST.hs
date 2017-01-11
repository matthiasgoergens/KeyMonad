{-# LANGUAGE Rank2Types,GeneralizedNewtypeDeriving #-}

module ST where 

import KeyM

import KeyMap
import Control.Monad.State
import Control.Applicative hiding (empty)
import Prelude hiding (lookup, (!))

type STRef s a = Key s a

newtype ST s a =
     ST (StateT (KeyMap s) (KeyM s) a)
  deriving (Functor,Applicative,Monad)


newSTRef :: a -> ST s (STRef s a)
newSTRef v = ST $ 
  do  k <- lift newKey
      modify (insert k v)
      return k

readSTRef :: STRef s a -> ST s a
readSTRef r = ST $ (! r) `fmap` get

writeSTRef :: STRef s a -> a -> ST s ()
writeSTRef k v = ST $ modify (insert k v)

unpack :: (forall s. ST s a) -> (forall s. StateT (KeyMap s) (KeyM s) a)
unpack (ST m) = m

runST :: (forall s. ST s a) -> a
runST m = runKeyM $ case m of
           ST n -> evalStateT n empty
 

