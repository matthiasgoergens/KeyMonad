{-# LANGUAGE NoMonomorphismRestriction, GADTs,  DataKinds,TypeOperators,RankNTypes, ScopedTypeVariables, FlexibleContexts,ImpredicativeTypes,KindSignatures, PolyKinds, TypeFamilies #-}
module KeyIM where

import Data.Type.Equality

type Key = Index
newtype KeyIM s t a = KeyIM { runKeyIM :: TList (Key s) t -> a }

newKey :: KeyIM s '[a] (Key s a) 
newKey = KeyIM $ \(h ::: _) -> h

type family (.++) a b where
  '[]      .++ b = b
  (h ': t) .++ b = h ': (t .++ b)

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
