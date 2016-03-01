{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators #-}
module SyntaxTranslate where

import HList
import KeyM
import HFMap
import Prelude hiding (lookup)

data PHoas f a where
    Var :: f a -> PHoas f a
    Lam :: (f a -> PHoas f b) -> PHoas f (a -> b)
    App :: PHoas f (a -> b) -> PHoas f a -> PHoas f b

type ClosedPHoas a = forall f. PHoas f a

data NHoas l a where
  NVar :: HIndex l a -> NHoas l a
  NLam :: NHoas (a ': t) b -> NHoas t (a -> b)
  NApp :: NHoas l (a -> b) -> NHoas l a -> NHoas l b

type ClosedNHoas a = NHoas '[] a

translate :: ClosedPHoas a -> ClosedNHoas a
translate t = runKeyM (go empty t)

go :: HFMap s (HIndex l)  -> PHoas (Key s) a -> KeyM s (NHoas l a)
go e (Var x) =
  pure $ NVar (e ! x)
go e (Lam f) =
   do k <- newKey
      let e' = insert k HHead (hfmapmap HTail e)
      b <- go e' (f k)
      return (NLam b)
go e (App f x) = NApp <$> go e f <*> go e x
