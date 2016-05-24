{-# LANGUAGE GADTs, AllowAmbiguousTypes, RankNTypes, DataKinds, TypeOperators, PolyKinds, TypeFamilies, UndecidableInstances #-}
import Unsafe.Coerce
import HList
import Data.Type.Equality


data Tree a = Leaf a | (Tree a) :*: (Tree a)

data p `Sub` w where
  Whole :: w `Sub` w
  LeftChild   :: (l :*: r) `Sub` w -> l `Sub` w
  RightChild   :: (l :*: r) `Sub` w -> r `Sub` w

testEq :: forall a b w. a `Sub` w -> b `Sub` w -> Maybe (a :~: b)
testEq Whole           Whole = Just Refl
testEq (LeftChild l)   (LeftChild r)  = weakenL <$> testEq l r
testEq (RightChild l)  (RightChild r) = weakenR <$> testEq l r
testEq _               _              = Nothing where 
  weakenL :: ((l :*: r) :~: (l' :*: r')) -> l :~: l'
  weakenL x = case x of Refl -> Refl

  weakenR :: ((l :*: r) :~: (l' :*: r')) -> r :~: r'
  weakenR x = case x of Refl -> Refl




data Key s a = Key (Sub (Leaf a) s)

instance TestEquality (Key s) where
  testEquality (Key l) (Key r) = 
     case testEq l r of
      Just Refl -> Just Refl
      Nothing   -> Nothing
                                   

type KeyIm l s a = Sub l s -> a

newKeyIm :: KeyIm (Leaf a) s (Key s a)
newKeyIm = Key

ireturn :: a -> KeyIm l s a
ireturn x = \_ -> x

runKeyIm :: (forall s. KeyIm l s a) -> a
runKeyIm f = f Whole

(.>>=) :: KeyIm l s a -> (a -> KeyIm r s b) -> KeyIm (l :*: r) s b
m .>>= f = \t -> f (m (LeftChild t)) (RightChild t)

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

