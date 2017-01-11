{-# LANGUAGE GADTs, AllowAmbiguousTypes, RankNTypes, DataKinds, TypeOperators, PolyKinds, TypeFamilies, UndecidableInstances #-}
import HList
import Data.Type.Equality
import Control.Applicative
import Control.Monad


data Tree a = Leaf a | (Tree a) :++: (Tree a)

data p `Sub` w where
  Start :: w `Sub` w
  LeftChild   :: (l :++: r) `Sub` w -> l `Sub` w
  RightChild   :: (l :++: r) `Sub` w -> r `Sub` w

testEq :: forall a b w. a `Sub` w -> b `Sub` w -> Maybe (a :~: b)
testEq Start           Start = Just Refl
testEq (LeftChild l)   (LeftChild r)  = weakenL <$> testEq l r
testEq (RightChild l)  (RightChild r) = weakenR <$> testEq l r
testEq _               _              = Nothing
weakenL :: ((l :++: r) :~: (l' :++: r')) -> l :~: l'
weakenL x = case x of Refl -> Refl

weakenR :: ((l :++: r) :~: (l' :++: r')) -> r :~: r'
weakenR x = case x of Refl -> Refl

type TName s a = Leaf a `Sub` s

type TNameSupply p s = Sub p s

newTNameSupply :: TNameSupply s s
newTNameSupply = Start

tsplit :: TNameSupply (l :++: r) s -> (TNameSupply l s, TNameSupply r s)
tsplit s = (LeftChild s, RightChild s)

supplyTName :: TNameSupply (Leaf a) s -> TName s a
supplyTName = id


data Key s a = Key (Sub (Leaf a) s)

instance TestEquality (Key s) where
  testEquality (Key l) (Key r) =
     case testEq l r of
      Just Refl -> Just Refl
      Nothing   -> Nothing


data KeyIm p s a = KeyIm { getKeyIm :: TNameSupply p s -> a }

newKeyIm :: KeyIm (Leaf a) s (Key s a)
newKeyIm = KeyIm $ \s -> Key (supplyTName s)



ireturn :: a -> KeyIm l s a
ireturn x = KeyIm $ \_ -> x

(.>>=) :: KeyIm l s a -> (a -> KeyIm r s b) -> KeyIm (l :++: r) s b
m .>>= f = KeyIm $ \s ->
        let (sl,sr) = tsplit s
        in getKeyIm (f (getKeyIm m sl)) sr

runKeyIm :: (forall s. KeyIm l s a) -> a
runKeyIm (KeyIm f) = f newTNameSupply

{-
data KeyM s a where
  KeyM :: KeyIm l s a -> KeyM s a

newKey :: KeyM s (Key s a)
newKey = KeyM $ newKeyIm

runKeyM :: (forall s. KeyM s a) -> a
runKeyM m = case m of
               KeyM f -> runKeyIm (unsafeCoerce f)

instance Functor (KeyM s) where fmap = liftM
instance Applicative (KeyM s) where pure = return; (<*>) = ap

instance Monad (KeyM s) where
  return = KeyM . ireturn
  m >>= f =
   case m of
    KeyM m' -> KeyM $ m' .>>= \x ->
           case f x of
              KeyM f' -> unsafeCoerce f'
-}

