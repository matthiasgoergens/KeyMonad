
{-# LANGUAGE Rank2Types, TypeOperators, GADTs,DataKinds, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}


import Control.Arrow
import qualified Control.Category as Cat
import KeyM
--import HFMap
import HMap
import HList



type Y x y = x -> y

strength :: Arrow a => (a x y,Y x z) -> a x (y,z)
strength (c, f) = (c &&& arr f)

rreturna :: Arrow a => Y x y -> a x y
rreturna f = arr f

bind :: Arrow a => a s x -> (forall s. Y s x -> a s y) -> a s y
bind r k = r >>> (k id)

monadify :: Arrow a => a x y -> (forall s. Y s x -> a s y)
monadify a x = (arr x >>> a)

arrowize :: Arrow a => (forall s. Y s x -> a s y) -> a x y
arrowize f = f id

newtype C x a = C (x -> a) deriving (Functor,Applicative)




newtype Cage s x = Cage (HMap s -> x) deriving (Functor,Applicative)
newtype Arm a s x = Arm { getArm :: KeyM s (a (HMap s) x) }

class RelativeMonad m v where
  rreturn   :: v a -> m a
  (.>>=)    :: m a -> (v a -> m b) -> m b


newtype Id a = Id a
instance Monad m => RelativeMonad m Id where
  rreturn (Id x) = return x
  m .>>= f = Id <$> m >>= f


toArm :: Arrow a => a x y -> Cage s x -> Arm a s y
toArm a (Cage f) = Arm (pure (arr f >>> a))

instance Arrow a => RelativeMonad (Arm a s) (Cage s) where
  rreturn (Cage f)   = Arm (pure (arr f))
  m .>>= f  = Arm $
    do al <- getArm m
       k <- newKey
       ar <- getArm (f (Cage (! k)))
       pure (extend al k >>> ar)

extend :: Arrow a => a (HMap s) y -> Key s y -> a (HMap s) (HMap s)
extend a k = a &&& arr id >>> arr (uncurry (insert k))


fromArm :: Arrow a => (forall s. Cage s x -> Arm a s y) -> a x y
fromArm f = runKeyM $
     do k <- newKey
        a <- getArm (f (Cage (! k)))
        return (arr (singleton k) >>> a)

class RelativeMonad m v => RelativeMonadPlus m v where
   rmzero :: m a
   rmplus :: m a -> m a -> m a

instance (ArrowZero a, ArrowPlus a) => RelativeMonadPlus (Arm a s) (Cage s) where
   rmzero = Arm (pure zeroArrow)
   rmplus l r  = Arm $
       do a <- getArm l
          b <- getArm r
          return (a <+> b)


newtype RelKleisli m v a b = RelKleisli {runK :: v a -> m b }

instance RelativeMonad m v => Cat.Category (RelKleisli m v) where
  id = RelKleisli $ rreturn
  g . f = RelKleisli (\x -> runK f x .>>= (runK g))

instance (Applicative v, RelativeMonad m v) => Arrow (RelKleisli m v) where
  arr f = RelKleisli (\x -> rreturn (f <$> x))
  first a = RelKleisli $ \t ->
     let x = fst <$> t
         y = snd <$> t
      in runK a x .>>= \x' ->
          rreturn ((,) <$> x' <*> y)

class RelativeMonad m v => RelativeMonadFix m v where
  rmfix :: (v a -> m a) -> m a


instance ArrowLoop a => RelativeMonadFix (Arm a s) (Cage s) where
  rmfix f = Arm $
     do k <- newKey
        a <- getArm (f (Cage (! k)))
        return (makeLoop a k)


makeLoop :: ArrowLoop a => a (HMap s) x -> Key s x -> a (HMap s) x
makeLoop a k = loop (makeLoopable a k)

makeLoopable :: Arrow a => a (HMap s) x -> Key s x -> a (HMap s,x) (x,x)
makeLoopable a k = arr (\(m,v) -> insert k v m) >>> a >>> arr (\x -> (x,x))




{-}
data Proc pa v a where
  RRet     :: v a -> Proc pa v a
  RBind    :: Proc pa v a -> (v a -> Proc pa v b) -> Proc pa v b
  Monadify :: pa x y -> v x -> Proc pa v y

data ProcE pa e x where
  Var      :: HIndex e x -> ProcE pa e x
  Bind     :: ProcE pa e x -> ProcE pa (x ': e) y -> ProcE pa e y
  EMonadify :: pa x y -> HIndex e x -> ProcE pa e y

runProc :: Arrow pa => (forall v. v x -> Proc pa v y) -> pa x y
runProc f = runKeyM $
  do k <- newKey
     r <- go (singleton k HHead) (f k)
     return (toSingleA >>> r)

toSingleA :: Arrow a => a x (HList '[x])
toSingleA = arr (\x -> HCons x Nil)

go :: Arrow pa => HFMap s (HIndex l) -> Proc pa (Key s) a -> KeyM s (pa (HList l) a)
go e (RRet k) = pure $ lookupA (e ! k)
go e (RBind m f) = do l <- go e m
                      k <- newKey
                      let e' = extendEnv k e
                      r <- go e' (f k)
                      pure $ extendA l >>> r
go e (Monadify a k) = pure $ monadifyA a (e ! k)

lookupA :: Arrow a => HIndex l x -> a (HList l) x
lookupA i = arr (\l -> index l i)

extendEnv :: Key s h -> HFMap s (HIndex t) -> HFMap s (HIndex (h ': t))
extendEnv k e = insert k HHead (hfmapmap HTail e)

extendA :: Arrow pa => pa (HList l) a -> pa (HList l) (HList (a ': l))
extendA a = (a &&& arr id) >>> arr (uncurry HCons)

monadifyA :: Arrow a => a x y -> HIndex l x -> a (HList l) y
monadifyA a i = lookupA i >>> a
-}
main = undefined
