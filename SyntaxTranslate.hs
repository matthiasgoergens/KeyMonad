{-# LANGUAGE GADTs, RankNTypes, TypeFamilies,DataKinds, KindSignatures,TypeOperators, NoMonomorphismRestriction #-}
module SyntaxTranslate where

import HList
import KeyM
import HFMap
import Prelude hiding (lookup, id, (.), fst,snd, curry, uncurry)
import Control.Category
import Unsafe.Coerce
import Control.Applicative hiding (empty)


class Hoas f where
    lam :: (f a -> f b) -> f (a -> b)
    app :: f (a -> b) -> f a -> f b

data PHoas f a where
    PVar :: f a -> PHoas f a
    PLam :: (f a -> PHoas f b) -> PHoas f (a -> b)
    PApp :: PHoas f (a -> b) -> PHoas f a -> PHoas f b

instance Hoas (PHoas f) where
    lam f = PLam (f . PVar)
    app = PApp

type ClosedPHoas a = forall f. PHoas f a



data NSyn l a where
  NVar :: Index l a -> NSyn l a
  NLam :: NSyn (a ': l) b -> NSyn l (a -> b)
  NApp :: NSyn l (a -> b) -> NSyn l a -> NSyn l b

type ClosedNHoas a = NSyn '[] a


data KeyLam s a where
  KVar :: Key s a -> KeyLam s a
  KLam :: Key s a -> KeyLam s b -> KeyLam s (a -> b)
  KApp :: KeyLam s (a -> b) -> KeyLam s a -> KeyLam s b

newtype HoasKey s a = HK { getExp :: KeyM s (KeyLam s a) }

instance Hoas (HoasKey s) where
  lam f = HK $
     do k <- newKey
        b <- getExp (f (HK (pure $ KVar k)))
        return $ KLam k b
  app f x = HK $ KApp <$> getExp f <*> getExp x

phoasToKey :: (forall v. PHoas v a) -> (forall s. KeyM s (KeyLam s a))
phoasToKey v = getExp (go v) where
  go :: PHoas (HoasKey s) a -> HoasKey s a
  go (PVar v) = v
  go (PLam f) = lam (go . f)
  go (PApp f x) = app (go f) (go x)

makeMorePrecise :: (forall s. KeyM s (KeyLam s x)) -> NSyn '[] x
makeMorePrecise  m = runKeyM (toNSyn <$> m)

toNSyn :: KeyLam s a -> NSyn '[] a
toNSyn = translate empty

type FKeyMap = HFMap

extend :: Key s h -> FKeyMap s (Index t) ->  FKeyMap s (Index (h ': t))
extend k m = insert k Head (pfmap Tail m)

translate :: HFMap s (Index l) -> KeyLam s a -> NSyn l a
translate e (KVar v)   = NVar (e ! v)
translate e (KLam k b) = NLam (translate (extend k e) b)
translate e (KApp f x) = NApp (translate e f) (translate e x)


{-
toNominal :: Hoas h => PHoas h a -> KeyM s (Nominal s a)
toNominal (Var x) = pure $ KVar x
toNominal (Lam f) = do k <- newKey
                       b <- toNominal (f k)
                       pure (KLam k b)
toNominal (App f x) = KApp <$> toNominal f <*> toNominal x
-}

{-
weakenNas :: Nas l a -> Nas (Snoc l a) a
weakenNas (NVar i) = NVar ( i)
-}
--weakenNas (NLam b) = NLam (weakenNas b)
--weakenNas (NApp f x) = NApp (weakenNas f) (weakenNas x)

-- translate :: Nominal s a ->

{-
translate :: ClosedPHoas a -> ClosedNHoas a
translate t = runKeyM (go empty t) where
  go :: HFMap s (HIndex l)  -> PHoas (Key s) a -> KeyM s (NSyn l a)
  go e (Var x) =
    pure $ NVar (e ! x)
  go e (Lam f) =
     do k <- newKey
        let e' = insert k HHead (hfmapmap HTail e)
        b <- go e' (f k)
        return (NLam b)
  go e (App f x) = NApp <$> go e f <*> go e x
-}
{-}
type Index = HIndex

data NSyn l a where
  NVar :: HIndex l a -> NSyn l a
  NLam :: NSyn (a ': l) b -> NSyn l (a -> b)
  NApp :: NSyn l (a -> b) -> NSyn l a -> NSyn l b

toClosed :: CCC c => NSyn '[] (x -> y) -> c () (x -> y)
toClosed p = go p TNil where
  go :: CCC c => NSyn l y -> TList (c x) l -> c x y
  go (NVar x) e = findex e x
  go (NLam b) e = curry $ go b (TCons snd (tmap (. fst) e))
  go (NApp f x) e = uncurry (go f e) . prod id (go x e)

app :: CCC c => c x (a -> b) -> c x a -> c x b
app f x = uncurry f . (prod id x)


class Category c => CCC c where
    prod    :: c x a -> c x b -> c x (a,b)
    fst     :: c (a,b) a
    snd     :: c (a,b) b
    curry   :: c (a,b) x -> c a (b -> x)
    uncurry :: c a (b -> x) -> c (a,b) x

data TList f l where
  TNil :: TList f '[]
  TCons :: f h -> TList f t -> TList f (h ': t)

tindex :: TList f l -> Index l x -> f x
tindex (TCons h _) HHead     = h
tindex (TCons _ t) (HTail i) = tindex t i

tmap :: (forall x. f x -> g x) -> TList f l -> TList g l
tmap f TNil        = TNil
tmap f (TCons h t) = TCons (f h) (tmap f t)

-}


type ClosedHoas a = forall f. Hoas f => f a



toPHoas :: ClosedHoas a -> ClosedPHoas a
toPHoas v = v

--doesNotOccur :: HIndex l a -> Nas l a -> Maybe (forall a. HIndex l a -> )

-- eta :: Nas l (a -> b) -> Nas l (a -> b)
--eta (NLam (NApp x HHead)) = x

test = lam $ \x -> lam $ \y -> x
