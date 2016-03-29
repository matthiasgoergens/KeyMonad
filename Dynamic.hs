{-# LANGUAGE Rank2Types,GADTs, KindSignatures, DataKinds #-}
module Dynamic where

import KeyM

data Dynamic tr where
  Dynamic :: tr a -> a -> Dynamic tr

toDynamic :: TestEquality v => v a -> a -> Dynamic v
toDynamic = Dynamic

fromDynamic :: TestEquality v => v a -> Dynamic v -> Maybe a
fromDynamic k (Dynamic k' a) =
   case testEquality k' k of
        Just x -> Just (castWith x a)
        Nothing -> Nothing

data FDynamic te f where
  FDynamic :: te a -> f a -> FDynamic te f

toFDynamic :: TestEquality v => v a -> f a -> FDynamic v f
toFDynamic = FDynamic

fromFDynamic :: TestEquality v => v a -> FDynamic v f -> Maybe (f a)
fromFDynamic k (FDynamic k' a) =
   case testEquality k' k of
        Just x -> Just (gcastWith x a)
        Nothing -> Nothing

fmapf :: (forall x. f x -> g x) -> FDynamic v f -> FDynamic v g
fmapf f (FDynamic v x) = FDynamic v (f x)
