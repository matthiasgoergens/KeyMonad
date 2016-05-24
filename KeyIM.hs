{-# LANGUAGE NoMonomorphismRestriction, GADTs,  DataKinds,TypeOperators,RankNTypes, ScopedTypeVariables, TypeFamilyDependencies, FlexibleContexts,ImpredicativeTypes,KindSignatures, PolyKinds, TypeFamilies #-}
module KeyIM where

import Data.Type.Equality

{-
type Key = Index
newtype KeyIM s t a = KeyIM { runKeyIM :: TList (Key s) t -> a }

newKey :: KeyIM s '[a] (Key s a) 
newKey = KeyIM $ \(h ::: _) -> h
-}

type family Not (a :: Bool) = (res :: Bool) | res -> a

{-
data SubList l r where
  Whole     :: SubList l l
  TrimLeft  :: SubList (l .++ r) x -> SubList l x
  TrimRight :: SubList (l .++ r) x -> SubList r x
-}
type family Plus (a :: [*]) (b :: [*]) = (r :: [*]) | Plus a -> b  where
  Plus '[] b = b
  Plus (h ': t) r = h ': Plus t r


{-
  '[]      .++ b = b
  (h ': t) .++ b = h ': (t .++ b)

weakenL :: ((l .++ r) :~: (l' .++ r)) -> l :~: l'
weakenL x = case x of
             Refl -> Refl
-}
{-
weakenR :: (Node l r :~: Node l' r') -> r :~: r'
weakenR x = case x of
             Refl -> Refl
-}
{-
testEq :: forall a b w. SubTree a w -> SubTree b w -> Maybe (a :~: b)
testEq End End = Just Refl
testEq (L l) (L r) = weakenL <$> testEq l r
testEq (R l) (R r) = weakenR <$> testEq l r
testEq _     _     = Nothing

class IsList l where
  makeKeys :: TList (Key l) l
  split    :: TList f (l .++ r) -> (TList f l, TList f r)

instance IsList '[] where
  makeKeys   = TNil
  split r    = (TNil, r)
instance IsList t => IsList (h ': t) where
  makeKeys        = Head ::: pfmap Tail makeKeys
  split (h ::: t) = let (l,r) = split t
                    in (h ::: l, r)

runKeyIm :: IsList l => (forall s. KeyIM s l a) -> a
runKeyIm (KeyIM m) = m makeKeys

ireturn :: a -> KeyIM s '[] a
ireturn x = KeyIM $ \_ -> x

(.>>=) :: IsList l => KeyIM s l a -> (a -> KeyIM s r b) -> KeyIM s (l .++ r) b
(.>>=) m f = KeyIM $ \t ->
         let (lk,rk) = split t
             x = runKeyIM m lk
         in runKeyIM (f x) rk
-}
