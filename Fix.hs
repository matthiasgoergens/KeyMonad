{-# LANGUAGE GADTs #-}
module Fix where

import Data.Maybe
import KeyM hiding ( apply )

--------------------------------------------------------------------------------

data Box s where
  Lock :: Key s a -> a -> Box s

unlock :: Key s a -> Box s -> Maybe a
unlock k (Lock k' x) =
  case testEquality k k' of
    Just Refl -> Just x
    Nothing   -> Nothing

--------------------------------------------------------------------------------

data D s a
  = Fun (Box s -> D s a)
  | Val a

fun :: Key s (D s a) -> (D s a -> D s a) -> D s a
fun k f = Fun (f . fromJust . unlock k)

apply :: Key s (D s a) -> D s a -> D s a -> D s a
apply k (Fun f) x = f (Lock k x)

fix :: (a -> a) -> a
fix f = runKeyM
  (do  k <- newKey
       let f' = Val . f . unVal
           wf = fun k (\x -> apply k (fun k f') (apply k x x))
       return (unVal (apply k wf wf)))
 where
  unVal (Val x) = x

