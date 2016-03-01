{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators #-}

module HList where

import Data.Type.Equality


data HList l where
  Nil   :: HList '[]
  HCons :: h -> HList t -> HList (h ': t)

data HIndex l a where
  HHead :: HIndex (h ': t) h
  HTail :: HIndex t x -> HIndex (h ': t) x

index :: HList l -> HIndex l a -> a
index (HCons h _) HHead     = h
index (HCons _ t) (HTail i) = index t i

instance TestEquality (HIndex l) where
  testEquality HHead     HHead     = Just Refl
  testEquality (HTail l) (HTail r) = testEquality l r
  testEquality _         _         = Nothing
