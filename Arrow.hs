
{-# LANGUAGE Rank2Types, FunctionalDependencies, TypeOperators, GADTs,DataKinds, DeriveFunctor,FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}


import Control.Arrow
import qualified Control.Category as Cat
import KeyM
import KeyMap
import Control.Applicative

import Control.Monad.Writer
import Data.Monoid

newtype Cage s x = Cage { liberate :: KeyMap s -> x }
  deriving (Functor, Applicative)

newtype ArrowSyn a s x =
    AS (WriterT (EndoA a (KeyMap s)) (KeyM s) x)
       deriving (Functor,Applicative,Monad)

newtype EndoA a x = EndoA (a x x)

instance Arrow a => Monoid (EndoA a x) where
    mempty = EndoA (arr id)
    mappend (EndoA l) (EndoA r) = EndoA (l >>> r)

toCage :: Key s a -> Cage s a
toCage k = Cage (\env -> env ! k)

introEnv :: Arrow a => Key s x -> a x (KeyMap s)
introEnv k = arr (singleton k)

elimEnv :: Arrow a => Cage s x -> a (KeyMap s) x
elimEnv c = arr (liberate c)

extendEnv :: Arrow a =>  Key s x ->
                         a (x, KeyMap s) (KeyMap s)
extendEnv k = arr (uncurry (insert k))

withEnv :: Arrow a =>  Cage s x ->
                       a (KeyMap s) (x, KeyMap s)
withEnv c = dup >>> first (elimEnv c)
    where dup = arr (\x -> (x,x))

toEnvA ::  Arrow a =>  
           Cage s x  -> Key s y   -> 
           a x y -> a (KeyMap s) (KeyMap s)
toEnvA inC outK a  =
   withEnv inC >>> first a >>> extendEnv outK

(-<) :: Arrow a =>
        a x y ->
        (Cage s x -> ArrowSyn a s (Cage s y))
a -< inC = AS $
   do  outK <- lift newKey
       tell (EndoA $ toEnvA inC outK a)
       return (toCage outK)

fromEnvA ::  Arrow a =>
             Key s x   -> Cage s y  ->
             a (KeyMap s) (KeyMap s) -> a x y
fromEnvA inK outC a  =
   introEnv inK >>> a >>> elimEnv outC

proc ::  Arrow a =>
             (forall s. Cage s x -> ArrowSyn a s (Cage s y)) ->
             a x y
proc f = runKeyM $
      do  inK <- newKey
          let AS m = f (toCage inK)
          (outC, EndoA a) <- runWriterT m
          return (fromEnvA inK outC a)

makeLoopable :: ArrowLoop a => Key s x -> Cage s x -> a (KeyMap s) (KeyMap s) -> a (KeyMap s, x) (KeyMap s, x)
makeLoopable k c a = flip >>> extendEnv k >>> a >>> withEnv c >>> flip
  where flip = arr (\(x,y) -> (y,x))


afix :: ArrowLoop a => (Cage s x -> ArrowSyn a s (Cage s x)) -> ArrowSyn a s (Cage s x)
afix f = AS $
  do k <- lift newKey
     let AS m = f (toCage k)
     (outC, EndoA a) <- lift $ runWriterT m
     tell (EndoA $ loop (makeLoopable k outC a))
     return (toCage k)
   


-- relative monads


class RelativeMonad m v | m -> v where
  rreturn   :: v a -> m a
  (.>>=)    :: m a -> (v a -> m b) -> m b
  -- laws (same as monad)
data Id a = Id a
data IdF m a = IdF {getIdf :: m a }

-- every monad is a relative monad
instance (Functor m, Applicative m, Monad m) => RelativeMonad (IdF m) Id where
  rreturn (Id x) = IdF $ return x
  (IdF m) .>>= f = IdF $ Id <$> m >>= getIdf . f

-- every relative monad is a monad via the following trick: (Svenningsson and Svensson), who did not 
-- formulate it as such
data RmSyn rm v a where
  Ret  :: a -> RmSyn rm v a
  Lift :: rm a -> RmSyn rm v (v a)
  Bind :: RmSyn rm v a -> (a -> RmSyn rm v b) -> RmSyn rm v b

desugar :: RelativeMonad rm v => RmSyn rm v (v a) -> rm a
desugar (Ret x) = rreturn x
-- remove pure computations
desugar (Bind (Ret x) f) = desugar (f x)
desugar (Bind (Lift m) f) = m .>>= (desugar . f)


class RelativeMonad m v => RelativeMonadFix m v where
  rmfix :: (v a -> m a) -> m a
  -- laws (same as monadfix without purity, + right shrinking):
   -- Laws
    -- left shrinking   : rmfix (\x -> a .>>= \y -> f x y) = a .>>= \y -> rmfix (\x -> f x y)
    -- right shrinking  : rmfix (λ(x , y). f x .>>= λz. g z .>>= λw. return (z , w))
    --                     = rmfix f .>>= λz. g z .>>= λw. return (z , w)
    -- rmfix (λx. f x .>>= return · h) = rmfix (f · h) .>>= return · h
    -- nesting : rmfix (\x -> rmfix (\y -> f x y)) = rmfix (\x -> f x x)

-- arrow relative monad
data Arm a s x = Arm { getArm :: ArrowSyn a s (Cage s x) }

instance Arrow a => RelativeMonad (Arm a s) (Cage s) where
  rreturn x = Arm (return x)
  m .>>= f  = Arm $ getArm m >>= getArm . f

instance ArrowLoop a => RelativeMonadFix (Arm a s) (Cage s) where
  rmfix f = Arm $ afix (getArm . f)

-- relative kleisli construction
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

instance (Applicative v, RelativeMonad m v, RelativeMonadFix m v) => ArrowLoop (RelKleisli m v) where
   loop (RelKleisli f) = RelKleisli $ makeLoop f
        

makeLoop :: (Applicative v, RelativeMonadFix m v) => (v (x,z) -> m (y,z)) -> v x -> m y
makeLoop f x = liftRm fst (rmfix (\y -> f $ (,) <$> x <*> (snd <$> y)))

liftRm :: (Applicative v, RelativeMonad m v) => (a -> b) -> m a -> m b
liftRm f m = m .>>= \x -> rreturn (f <$> x)


-- Altenkirch et al.'s construction:
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


{-




toArm :: Arrow a => a x y -> Cage s x -> Arm a s y
toArm a c = Arm (a -< c)



-}

{-
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




class RelativeMonad m v => RelativeMonadFix m v where
  rmfix :: (v a -> m a) -> m a







-}

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
