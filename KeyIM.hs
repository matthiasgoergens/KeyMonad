{-# LANGUAGE NoMonomorphismRestriction, GADTs,  DataKinds,TypeOperators,RankNTypes, ScopedTypeVariables, FlexibleContexts,ImpredicativeTypes,KindSignatures, PolyKinds, TypeFamilies #-}
module KeyIM where

import Data.Type.Equality

-- This bit stolen from : https://hackage.haskell.org/package/effect-monad-0.6.1

{-| Specifies "parametric effect monads" which are essentially monads but
     annotated by a type-level monoid formed by 'Plus' and 'Unit' -}
class IMonad (m :: k -> * -> *) where

   {-| Effect of a trivially effectful computation |-}
   type Unit m :: k
   {-| Cominbing effects of two subcomputations |-}
   type Plus m (f :: k) (g :: k) :: k

   {-| Effect-parameterised version of 'return'. Annotated with the 'Unit m' effect,
    denoting pure compuation -}
   ireturn :: a -> m (Unit m) a

   {-| Effect-parameterise version of '>>=' (bind). Combines
    two effect annotations 'f' and 'g' on its parameter computations into 'Plus' -}
   (.>>=) :: m f a -> (a -> m g b) -> m (Plus m f g) b

   (.>>) :: m f a -> m g b -> m (Plus m f g) b
   x .>> y = x .>>= (\_ -> y)

data Proxy a = Proxy

data List a =
   Nil | Single a  | App (List a) (List a)

data TList f l where
  HNil :: TList f Nil
  HSingle  :: f h -> TList f (Single h)
  HApp   :: TList f l -> TList f r -> TList f (App l r)

ffmap :: (forall x. f x -> g x) -> TList f ls -> TList g ls
ffmap f HNil = HNil
ffmap f (HSingle h) = HSingle (f h)
ffmap f (HApp l r)   = HApp (ffmap f l) (ffmap f r)

makeKeys :: TList Proxy l -> TList (Key l) l
makeKeys HNil = HNil
makeKeys (HSingle h) = HSingle KSingle
makeKeys (HApp l r) = HApp (ffmap KLeft (makeKeys l)) (ffmap KRight (makeKeys r))


data Key l a where
  KSingle:: Key (Single h) h
  KLeft  :: Key l a -> Key (App l r) a
  KRight :: Key r a -> Key (App l r) a


tleft :: TList f (App l r) -> TList f l
tleft (HApp l r) = l

tright :: TList f (App l r) -> TList f r
tright (HApp l r) = r

tsingle :: TList f (Single x) -> f x
tsingle (HSingle x) = x

instance TestEquality (Key l) where
  testEquality KSingle     KSingle     = Just Refl
  testEquality (KLeft ll)  (KLeft lr)  = testEquality ll lr
  testEquality (KRight rl) (KRight rr) = testEquality rl rr
  testEquality _           _           = Nothing


{- Indexed monad variant (type safe in Haskell)

This is exactly http://www.cl.cam.ac.uk/~dao29/publ/haskell14-effects.pdf


The monad is indexed by the types which are created in the rest of the computation.

-}

-- Produce the list of types that is needed for a computation, and consume the Keys
newtype KeyIM l t a = KeyIM {
      getKeyIM :: TList (Key l) t -> (a, TList Proxy t)
    }

instance IMonad (KeyIM l) where
  type Unit (KeyIM l) = Nil
  type Plus (KeyIM l) x y = App x y

  ireturn x = KeyIM $ \_ -> (x, HNil)

  m .>>= f = KeyIM $ \k ->
     let (x, pl) = getKeyIM m (tleft k)
         (y, pr) = getKeyIM (f x) (tright k)
     in (y, HApp pl pr)


newKey :: KeyIM s (Single a) (Key s a)
newKey = KeyIM $ \k -> (tsingle k, HSingle Proxy)


runKeyIM :: (forall l. KeyIM l t a) -> a
runKeyIM k = let (x,ps) = getKeyIM k (makeKeys ps)
             in x
