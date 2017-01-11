{-# LANGUAGE Rank2Types, FunctionalDependencies, TypeOperators, GADTs,DataKinds, DeriveFunctor,FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Arrow where

import Control.Arrow
import qualified Control.Category as Cat
import KeyM
import KeyMap
import Control.Applicative

import Control.Monad.Writer
import Data.Monoid

newtype Cage s x = Cage { open :: KeyMap s -> x }
  deriving (Functor, Applicative)

newtype ArrowSyntax a s x =
    AS (WriterT (EnvArrow a s) (KeyM s) x)
       deriving (Functor,Applicative,Monad)

newtype EnvArrow a s = EnvArrow (a (KeyMap s) (KeyMap s))

instance Arrow a => Monoid (EnvArrow a x) where
    mempty = EnvArrow (arr id)
    mappend (EnvArrow l) (EnvArrow r) = EnvArrow (l >>> r)

toCage :: Key s a -> Cage s a
toCage k = Cage (\env -> env ! k)

introEnv :: Arrow a => Key s x -> a x (KeyMap s)
introEnv k = arr (singleton k)

elimEnv :: Arrow a => Cage s x -> a (KeyMap s) x
elimEnv c = arr (open c)

extendEnv :: Arrow a =>  Key s x ->
                         a (x, KeyMap s) (KeyMap s)
extendEnv k = arr (uncurry (insert k))

withEnv :: Arrow a =>  Cage s x ->
                       a (KeyMap s) (x, KeyMap s)
withEnv c = dup >>> first (elimEnv c)
    where dup = arr (\x -> (x,x))

toEnvArrow ::  Arrow a =>
           Cage s x  -> Key s y   ->
           a x y -> EnvArrow a s
toEnvArrow inC outK a  = EnvArrow $
   withEnv inC >>> first a >>> extendEnv outK

(-<) :: Arrow a =>
        a x y ->
        (Cage s x -> ArrowSyntax a s (Cage s y))
a -< inC = AS $
   do  outK <- lift newKey
       tell (toEnvArrow inC outK a)
       return (toCage outK)

fromEnvArrow ::  Arrow a =>
             Key s x   -> Cage s y  ->
             EnvArrow a s -> a x y
fromEnvArrow inK outC (EnvArrow a)  =
   introEnv inK >>> a >>> elimEnv outC

proc ::  Arrow a =>
             (forall s. Cage s x -> ArrowSyntax a s (Cage s y)) ->
             a x y
proc f = runKeyM $
      do  inK <- newKey
          let AS m = f (toCage inK)
          (outC, a) <- runWriterT m
          return (fromEnvArrow inK outC a)

makeLoopable :: ArrowLoop a => Key s x -> Cage s x -> a (KeyMap s) (KeyMap s) -> a (KeyMap s, x) (KeyMap s, x)
makeLoopable k c a = flip >>> extendEnv k >>> a >>> withEnv c >>> flip
  where flip = arr (\(x,y) -> (y,x))


afix :: ArrowLoop a => (Cage s x -> ArrowSyntax a s (Cage s x)) -> ArrowSyntax a s (Cage s x)
afix f = AS $
  do k <- lift newKey
     let AS m = f (toCage k)
     (outC, EnvArrow a) <- lift $ runWriterT m
     tell (EnvArrow $ loop (makeLoopable k outC a))
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
data RelativeMSyntax rm v a where
   Pure :: a -> RelativeMSyntax rm v a
   Unpure ::  rm a -> (v a -> RelativeMSyntax rm v b)
              -> RelativeMSyntax rm v b

instance Monad (RelativeMSyntax rm v) where
  return = Pure
  (Pure x) >>= f = f x
  (Unpure m f) >>= g = Unpure m (\x -> f x >>= g)

fromRelativeM :: RelativeMonad rm v =>
   rm a -> RelativeMSyntax rm v (v a)
fromRelativeM m = Unpure m return

toRelativeM :: RelativeMonad rm v =>
                  RelativeMSyntax rm v (v a) -> rm a
toRelativeM (Pure x)      = rreturn x
toRelativeM (Unpure m f)  = m .>>= (toRelativeM . f)


-- not really a monad, but up to observation

data RmSyn rm v a where
  Ret  :: a -> RmSyn rm v a
  Lift :: rm a -> RmSyn rm v (v a)
  Bind :: RmSyn rm v a -> (a -> RmSyn rm v b) -> RmSyn rm v b

instance Monad (RmSyn rm v) where
  return = Ret
  (>>=)  = Bind

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
data Arm a s x = Arm { getArm :: ArrowSyntax a s (Cage s x) }

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


