
{-# LANGUAGE Rank2Types, TypeOperators, GADTs,DataKinds #-}

import Control.Arrow

import KeyM
import HFMap
import HList



type Y x y = x -> y

strength :: Arrow pa => (pa x y,Y x z) -> pa x (y,z)
strength (c, f) = (c &&& arr f)

rreturn :: Arrow pa => Y x y -> pa x y
rreturn f = arr f

bind :: Arrow pa => pa s' x -> (forall s. Y s x -> pa s y) -> pa s' y
bind r k = r >>> (k id)

monadify :: Arrow a => a x y -> (forall s. Y s x -> a s y)
monadify a x = (arr x >>> a)

arrowize :: Arrow a => (forall s. Y s x -> a s y) -> a x y
arrowize f = f id

extend :: Arrow a => a x y -> (forall s. Y s x -> a s (y,x))
extend a x = strength (monadify a x, x)

data Proc pa v a where
  RRet     :: v a -> Proc pa v a
  RBind    :: Proc pa v a -> (v a -> Proc pa v b) -> Proc pa v b
  Monadify :: pa x y -> v x -> Proc pa v y



extendA :: Arrow pa => pa (HList l) a -> pa (HList l) (HList (a ': l))
extendA a = (a &&& arr id) >>> arr (uncurry HCons)

runProc :: Arrow pa => (forall v. v x -> Proc pa v y) -> pa x y
runProc f = undefined

go :: Arrow pa => HFMap s (HIndex l) -> Proc pa (Key s) a -> KeyM s (pa (HList l) a)
go e (RRet k) = pure $ arr (\l -> index l (e ! k))
go e (RBind m f) = do l <- go e m
                      k <- newKey
                      let e' = insert k HHead (hfmapmap HTail e)
                      r <- go e' (f k)
                      pure $ extendA l >>> r
go e (Monadify a k) = pure $ arr (\l -> index l (e ! k)) >>> a

main = undefined
