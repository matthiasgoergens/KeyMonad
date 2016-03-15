
{-# LANGUAGE Rank2Types, TypeOperators, GADTs,DataKinds #-}

import Control.Arrow

import KeyM
import HFMap
import HList



type Y x y = x -> y

strength :: Arrow a => (a x y,Y x z) -> a x (y,z)
strength (c, f) = (c &&& arr f)

rreturn :: Arrow a => Y x y -> a x y
rreturn f = arr f

bind :: Arrow a => a s x -> (forall s. Y s x -> a s y) -> a s y
bind r k = r >>> (k id)

monadify :: Arrow a => a x y -> (forall s. Y s x -> a s y)
monadify a x = (arr x >>> a)

arrowize :: Arrow a => (forall s. Y s x -> a s y) -> a x y
arrowize f = f id


data Proc pa v a where
  RRet     :: v a -> Proc pa v a
  RBind    :: Proc pa v a -> (v a -> Proc pa v b) -> Proc pa v b
  Monadify :: pa x y -> v x -> Proc pa v y

data ProcE pa e x where
  Var      :: HIndex e x -> ProcE pa e x
  Bind     :: ProcE pa e x -> ProcE pa (x ': e) y -> ProcE pa e y
  Monadify :: pa x y -> HIndex e x -> ProcE pa e y

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

main = undefined
