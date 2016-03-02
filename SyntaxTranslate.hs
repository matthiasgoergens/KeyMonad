{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators #-}
module SyntaxTranslate where

import HList
import KeyM
import HFMap
import Prelude hiding (lookup, id, (.), fst,snd, curry, uncurry)
import Control.Category

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
translate t = runKeyM (go empty t) where
  go :: HFMap s (HIndex l)  -> PHoas (Key s) a -> KeyM s (NHoas l a)
  go e (Var x) =
    pure $ NVar (e ! x)
  go e (Lam f) =
     do k <- newKey
        let e' = insert k HHead (hfmapmap HTail e)
        b <- go e' (f k)
        return (NLam b)
  go e (App f x) = NApp <$> go e f <*> go e x


class Category c => Prod c where
  prod :: c x a -> c x b -> c x (a,b)
  fst :: c (a,b) a
  snd :: c (a,b) b

class Prod c => Closed c where
  curry :: c (a,b) x -> c a (b -> x)
  uncurry :: c a (b -> x) -> c (a,b) x

app :: Closed c => c x (a -> b) -> c x a -> c x b
app f x = uncurry f . (prod id x)

toClosed :: Closed c => NHoas (x ': '[]) y -> c x y
toClosed p = go p (FHCons id FNil) where
  go :: Closed c => NHoas l y -> HFList (c x) l -> c x y
  go (NVar x) e = findex e x
  go (NLam b) e = curry $ go b (FHCons snd (fhmap (. fst) e))
  go (NApp f x) e = app (go f e) (go x e)
