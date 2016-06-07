{-# LANGUAGE GADTs,GeneralizedNewtypeDeriving #-}

module Box where
import KeyM

data Box s where
  Lock :: Key s a -> a -> Box s

unlock :: Key s a -> Box s -> Maybe a
unlock k (Lock k' x) =
   case testEquality k k' of
    Just Refl  -> Just x
    Nothing    -> Nothing

