{-# LANGUAGE GADTs, AllowAmbiguousTypes, RankNTypes,TypeFamilyDependencies, DataKinds, TypeOperators, PolyKinds, TypeFamilies, UndecidableInstances #-}
import Unsafe.Coerce
import HList



data Tree a = Empty | Leaf a | Node (Tree a) (Tree a)

data SubTree a b where
  Whole   :: SubTree a a
  SLeft   :: SubTree (Node l r) s -> SubTree l s
  SRight  :: SubTree (Node l r) s -> SubTree r s

type Key s a = SubTree (Leaf a) s


type KeyIm l s a = SubTree l s -> a

newKeyIm :: KeyIm (Leaf a) s (Key s a)
newKeyIm = id

ireturn :: a -> KeyIm l s a
ireturn x = \_ -> x

runKeyIm :: (forall s. KeyIm l s a) -> a
runKeyIm f = f Whole

(.>>=) :: KeyIm l s a -> (a -> KeyIm r s b) -> KeyIm (Node l r) s b
m .>>= f = \t -> f (m (SLeft t)) (SRight t)

data KeyM s a where
  KeyM :: KeyIm l s a -> KeyM s a

newKey :: KeyM s (Key s a)
newKey = KeyM $ newKeyIm

runKeyM :: (forall s. KeyM s a) -> a
runKeyM m = case m of
               KeyM f -> runKeyIm (unsafeCoerce f)

instance Functor (KeyM s)
instance Applicative (KeyM s)

instance Monad (KeyM s) where
  return = KeyM . ireturn
  m >>= f = 
   case m of
    KeyM m' -> KeyM $ m' .>>= \x ->
           case f x of
              KeyM f' -> unsafeCoerce f'
