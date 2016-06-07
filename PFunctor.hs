{-# LANGUAGE RankNTypes #-}

module PFunctor where

class PFunctor p where
  pfmap :: (forall x. f x -> g x) -> p f -> p g
