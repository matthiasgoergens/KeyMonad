{-# LANGUAGE GADTs, RankNTypes, TypeFamilies,DataKinds, KindSignatures,TypeOperators, NoMonomorphismRestriction #-}
module SyntaxTranslate where

import HList
import KeyM
import HFMap
import Prelude hiding (lookup, id, (.), fst,snd, curry, uncurry)
import Control.Category
import Unsafe.Coerce


data PHoas f a where
    Var :: f a -> PHoas f a
    Lam :: (f a -> PHoas f b) -> PHoas f (a -> b)
    App :: PHoas f (a -> b) -> PHoas f a -> PHoas f b

instance Hoas (PHoas f) where
    lam f = Lam (f . Var)
    appl = App


type ClosedPHoas a = forall f. PHoas f a

data Nas l a where
  NVar :: HIndex l a -> Nas l a
  NLam :: Nas (a ': t) b -> Nas t (a -> b)
  NApp :: Nas l (a -> b) -> Nas l a -> Nas l b

type ClosedNHoas a = Nas '[] a

type family Snoc l (a :: *) :: [*] where
  Snoc '[] a = '[a]
  Snoc (h ': t) a = h ': (Snoc t a)

data K s a

data Syn f a where
      SVar    :: f a -> Syn f a
      SLam    :: (f a -> Syn f b) -> Syn f (a -> b)
      SApp    :: Syn f (a -> b) -> Syn f a -> Syn f b

      Convert :: Syn f (K f a) -> Syn f (Key f a) -> Syn f (Either () (a -> b))



{-
weakenNas :: Nas l a -> Nas (Snoc l a) a
weakenNas (NVar i) = NVar ( i)
-}
--weakenNas (NLam b) = NLam (weakenNas b)
--weakenNas (NApp f x) = NApp (weakenNas f) (weakenNas x)


translate :: ClosedPHoas a -> ClosedNHoas a
translate t = runKeyM (go empty t) where
  go :: HFMap s (HIndex l)  -> PHoas (Key s) a -> KeyM s (Nas l a)
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

toClosed :: Closed c => Nas (x ': '[]) y -> c x y
toClosed p = go p (FHCons id FNil) where
  go :: Closed c => Nas l y -> HFList (c x) l -> c x y
  go (NVar x) e = findex e x
  go (NLam b) e = curry $ go b (FHCons snd (fhmap (. fst) e))
  go (NApp f x) e = app (go f e) (go x e)


class Hoas f where
    lam :: (f a -> f b) -> f (a -> b)
    appl :: f (a -> b) -> f a -> f b

type ClosedHoas a = forall f. Hoas f => f a



toPHoas :: ClosedHoas a -> ClosedPHoas a
toPHoas v = v

--doesNotOccur :: HIndex l a -> Nas l a -> Maybe (forall a. HIndex l a -> )

-- eta :: Nas l (a -> b) -> Nas l (a -> b)
--eta (NLam (NApp x HHead)) = x

test = lam $ \x -> lam $ \y -> x
