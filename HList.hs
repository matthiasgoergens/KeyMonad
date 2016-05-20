{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators, PolyKinds, TypeFamilies, UndecidableInstances #-}

module HList where

import Data.Type.Equality


data HList l where
  Nil   :: HList '[]
  HCons :: h -> HList t -> HList (h ': t)


data TList f l where
  TNil  :: TList f '[] 
  (:::) :: f h -> TList f t -> TList f (h ': t)

instance TestEquality (Index l) where
  testEquality Head     Head     = Just Refl
  testEquality (Tail l) (Tail r) = testEquality l r
  testEquality _         _         = Nothing

data Index l a where
  Head :: Index (h ': t) h
  Tail :: Index t x -> Index (h ': t) x

hindex :: HList l -> Index l a -> a
hindex (HCons h _) Head     = h
hindex (HCons _ t) (Tail i) = hindex t i

index :: TList f l -> Index l a -> f a
index (h ::: _) Head     = h
index (_ ::: t) (Tail i) = index t i

pfmap :: (forall x. f x -> g x) -> TList f l -> TList g l
pfmap f TNil      = TNil
pfmap f (h ::: t) = f h ::: pfmap f t

{-
hhead :: HFList f (h ': t) -> f h
hhead (FHCons h _) = h
-}


{-
toHIndex :: Nat n -> HList l -> HIndex l (Index l n)
toHIndex SZ (HCons h _) = HHead
toHIndex (SS i) (HCons _ t) = HTail (toHIndex i t)

toIndex :: WellFormed l x -> HList l -> HIndex l x
toIndex (WellFormed i) = toHIndex i l
-}
