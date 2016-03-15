{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators, PolyKinds #-}

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
