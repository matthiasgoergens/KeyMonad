{-# LANGUAGE GADTs, Rank2Types, DataKinds, TypeOperators, KindSignatures, ImpredicativeTypes #-}
import Data.Type.Equality
import Control.Applicative
import Control.Monad
import Unsafe.Coerce
import Prelude hiding (Right,Left)	

data Tree a = Empty | Single a | Tree a :++: Tree a

data TTreePath (p :: Tree *) (w :: Tree *) where
  Start   :: TTreePath w w
  Left    :: TTreePath (l :++: r) w -> TTreePath l w
  Right   :: TTreePath (l :++: r) w -> TTreePath r w

samePath ::  TTreePath p w -> TTreePath p' w 
             -> Maybe (p :~: p')
-- fix this type error
samePath Start      Start      = Just Refl
samePath (Left l)   (Left r)   = weakL  <$> samePath l r
samePath (Right l)  (Right r)  = weakR  <$> samePath l r
samePath _          _          = Nothing 
 
weakL :: ((l :++: r) :~: (l' :++: r')) -> l :~: l'
weakL x = case x of Refl -> Refl
weakR :: ((l :++: r) :~: (l' :++: r')) -> r :~: r'
weakR x = case x of Refl -> Refl

sameLeaf ::  TTreePath (Single p) w ->
             TTreePath (Single p') w -> 
             Maybe (p :~: p')
sameLeaf l r = weakenLeaf <$> samePath l r where
  weakenLeaf :: (Single p :~: Single p') -> p :~: p'
  weakenLeaf x = case x of Refl -> Refl


type TNameSupply l s = TTreePath l s
type TName s a = TTreePath (Single a) s

newTNameSupply :: TNameSupply s s
newTNameSupply = Start 

tsplit ::  TNameSupply (l :++: r) s 
           -> (TNameSupply l s, TNameSupply r s)
tsplit s = (Left s, Right s)

supplyTName :: TNameSupply (Single a) s -> TName s a
supplyTName = id

sameName ::  TName s a -> TName s b -> 
             Maybe (a :~: b)
sameName = sameLeaf

type Key s a = TName s a

data KeyIM l s a where
  NewKey :: KeyIM (Single a) s (Key s a)
  Return :: a -> KeyIM Empty s  a
  Bind   :: KeyIM l s a -> (a -> KeyIM r s b) -> KeyIM (l :++: r) s b

interpret :: TNameSupply p w -> KeyIM p w a -> a
interpret ns s = 
  case s of 
    NewKey -> supplyTName ns
    Return x -> x
    Bind m f -> let (l,r) = tsplit ns
                in interpret r (f (interpret l m))

runKeyIM :: KeyIM s s a -> a
runKeyIM m = interpret newTNameSupply m



type AbsKeyM a = forall km s. 
       (forall a. km s (Key s a)) ->
       (forall a. a -> km s a) -> 
       (forall a b. km s a -> (a -> km s b) -> km s b) -> 
       km s a

-- atkey type reasoning: forall a. 
--   the denotation of type AbsKeyM a is isomorphic to
--    (exists s. KeyIM s s a) 
-- (for finite computations? What happens for infinite. Need infinite types?)
-- I don't know if this follows from a parametricity for GADTs + Kripke stuff


data ClosedKeyIM a where
  Closed :: KeyIM s s a -> ClosedKeyIM a

atKeyMagic :: AbsKeyM a -> ClosedKeyIM a
atKeyMagic f = Closed (f (unsafeCoerce NewKey) (unsafeCoerce Return) (unsafeCoerce Bind))

data KeyM s a where
  NK :: KeyM s (Key s a)
  Ret :: a -> KeyM s a
  Bnd :: KeyM s a -> (a -> KeyM s b) -> KeyM s b

toAbs :: (forall s. KeyM s a) -> AbsKeyM a
-- this should work.., fixme
--toAbs m = absGo m
toAbs m = undefined

absGo :: KeyM s a ->
       (forall a. km s (Key s a)) ->
       (forall a. a -> km s a) -> 
       (forall a b. km s a -> (a -> km s b) -> km s b) -> 
       km s a
absGo m nk ret bnd = case m of
       NK -> nk
       Ret x -> ret x
       Bnd m f -> bnd (absGo m nk ret bnd) (\x -> absGo (f x) nk ret bnd)

runKey :: (forall s . KeyM s a) -> a
runKey m = case atKeyMagic (toAbs m) of
             Closed m -> runKeyIM m


  

