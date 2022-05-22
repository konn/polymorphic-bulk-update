{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Record.PartialUpdate where

import Data.Functor.Dissectable
import Data.Vector (Vector)
import GHC.Exts (Proxy#, type (~~))
import GHC.Generics
import GHC.TypeLits (Symbol)

-- | A type @t a@, which is partially converted to @t b@
data Partial t a b (uninitialised :: [Symbol]) = Partial
  { original :: t a
  , -- TODO: consider exploiting linearity to avoid reallocation
    updates :: Vector (a -> b)
  }

type family Container f a where
  Container Par1 a = a
  Container (f :.: g) a = f (Container g a)
  Container (Rec1 t) a = t a
  Container (M1 i c f) a = Container f a

class GParametricLabel (l :: Symbol) t

class GParametric f

instance GParametric Par1

instance GParametric (Rec1 t)

instance GParametric g => GParametric (f :.: g)

instance GParametric f => GParametric (M1 i c f)

instance {-# OVERLAPPING #-} GParametricLabel l (M1 S ( 'MetaSel ml a b c) f)

instance {-# OVERLAPPING #-} GParametricLabel l f => GParametricLabel l (M1 i ( 'MetaSel ml a b c) f)

class SetField (l :: Symbol) s t a b | s l -> a, s l b -> t where
  updateField :: Proxy# l -> (a -> b) -> s -> t

instance (l ~~ sym, t ~~ u) => SetField l (Partial t a b '[sym]) (u b) a b

type Delete :: forall {k}. k -> k -> k -> [k] -> [k]
type family Delete x y y' ys where
  Delete l l k xs = k ': xs
  Delete l k l xs = k ': xs
  Delete l k k' '[] = '[k, k']
  Delete l k k' (l ': ks) = k ': k' ': ks
  Delete l k k' (k'' ': ks) = k ': Delete l k' k'' ks

instance
  ks' ~~ Delete l k k' cs =>
  SetField l (Partial t a b (k ': k' ': cs)) (Partial t a b ks') a b

instance SetField l (t a) (Partial t a b '[]) a b
