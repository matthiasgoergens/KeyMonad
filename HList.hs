{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators, PolyKinds, TypeFamilies, UndecidableInstances #-}

module HList where

import Data.Type.Equality


data HList l where
  Nil   :: HList '[]
  HCons :: h -> HList t -> HList (h ': t)

data HIndex2 l a where
  HIndex2 :: HIndex l r -> HIndex r a -> HIndex2 l a

data HFList f l where
    FNil   :: HFList f '[]
    FHCons :: f h -> HFList f t -> HFList f (h ': t)


data HIndex l a where
  HHead :: HIndex (h ': t) h
  HTail :: HIndex t x -> HIndex (h ': t) x

index :: HList l -> HIndex l a -> a
index (HCons h _) HHead     = h
index (HCons _ t) (HTail i) = index t i

findex :: HFList f l -> HIndex l a -> f a
findex (FHCons h _) HHead     = h
findex (FHCons _ t) (HTail i) = findex t i

index2 :: HFList HList l -> HIndex2 l a -> a
index2 l (HIndex2 i1 i2) = index (findex l i1) i2

fhmap :: (forall x. f x -> g x) -> HFList f l -> HFList g l
fhmap f FNil = FNil
fhmap f (FHCons h t) = FHCons (f h) (fhmap f t)



instance TestEquality (HIndex l) where
  testEquality HHead     HHead     = Just Refl
  testEquality (HTail l) (HTail r) = testEquality l r
  testEquality _         _         = Nothing

data N = S N | Z

data Nat (n :: N) where
  SZ :: Nat Z
  SS :: Nat x -> Nat (S x)

type family Snoc (l :: [*]) (x :: *) where
  Snoc '[] x = x ': '[]
  Snoc (h ':  t) x = h ': Snoc t x

type family Reverse (l :: [*]) where
  Reverse '[]      = '[]
  Reverse (h ': t) = Snoc (Reverse t) h

type family Index (l :: [*]) (i :: N) where
  Index (h ': t) Z = h
  Index (h ': t) (S i) = Index t i

data WellFormed l x where
  WellFormed :: Nat n -> WellFormed l (Index (Reverse l) n)

data PHoas v a where
  Var :: v a -> PHoas v a
{-
toHIndex :: Nat n -> HList l -> HIndex l (Index l n)
toHIndex SZ (HCons h _) = HHead
toHIndex (SS i) (HCons _ t) = HTail (toHIndex i t)

toIndex :: WellFormed l x -> HList l -> HIndex l x
toIndex (WellFormed i) = toHIndex i l
-}
