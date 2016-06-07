{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators, PolyKinds, TypeFamilies, UndecidableInstances #-}
import SyntaxTranslate
import Control.Category
import HList
import PFunctor
import Prelude hiding ((.),id, fst, snd, curry, uncurry)

class Category c => CCC c where
    prod     :: c x a -> c x b -> c x (a,b)
    fst      :: c (a,b) a
    snd      :: c (a,b) b
    curry    :: c (a,b) x -> c a (b -> x)
    uncurry  :: c a (b -> x) -> c (a,b) x

toClosed :: CCC c => Bruijn '[] (x -> y) -> c () (x -> y)
toClosed p = go p TNil where
  go :: CCC c => Bruijn l y -> TList l (c x) -> c x y
  go (BVar x)    e = index e x
  go (BLam b)    e = 
    curry $ go b (snd ::: pfmap (. fst) e)
  go (BApp f x)  e = uncurry (go f e) . prod id (go x e)

instance PFunctor (TList l) where
  pfmap f TNil      = TNil
  pfmap f (h ::: t) = f h ::: pfmap f t
