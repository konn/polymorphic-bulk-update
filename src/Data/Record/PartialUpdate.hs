{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Record.PartialUpdate where

import Data.Coerce (Coercible)
import Data.Functor.Dissectable
import Data.Kind (Type)
import Data.Type.Coercion (Coercion (..), gcoerceWith)
import Data.Vector (Vector)
import GHC.Exts (Proxy#, proxy#, type (~~))
import GHC.Generics
import GHC.TypeLits (Symbol)
import GHC.TypeNats

-- | A type @t a@, which is partially converted to @t b@
data Partial t a b (uninitialised :: [Symbol]) = Partial
  { original :: t a
  , -- TODO: consider exploiting linearity to avoid reallocation
    updates :: Vector (a -> b)
  }

class
  (forall x y. Coercible x y => Coercible (g x) (g y)) =>
  Representational g

instance
  (forall x y. Coercible x y => Coercible (g x) (g y)) =>
  Representational g

type family Flatten (f :: Type -> Type) a :: Type where
  Flatten (M1 i c f) a = f a
  Flatten (g :.: f) a = g (Flatten f a)
  Flatten Par1 a = a
  Flatten (Rec1 t) a = t a

class SetField (l :: Symbol) s t a b | s l -> a, s l b -> t where
  updateField :: Proxy# l -> (a -> b) -> s -> t

data GPos = There Nat | Here Nat (Type -> Type)

type family (<|>) ma mb where
  'There n <|> 'There m = 'There (n + m)
  'There n <|> 'Here m a = 'Here (n + m) a
  'Here n a <|> _ = 'Here n a

type RawFieldOf :: Symbol -> (Type -> Type) -> GPos
type family RawFieldOf l p where
  RawFieldOf l (M1 S ( 'MetaSel ( 'Just l) _a _b _c) f) =
    OnPos (CountPar f) f
  RawFieldOf l (M1 S _ f) = 'There (CountPar f)
  RawFieldOf l (M1 i c f) = RawFieldOf l f
  RawFieldOf l (f :*: g) =
    RawFieldOf l f <|> RawFieldOf l g

type family OnPos n f where
  OnPos 1 f = 'Here 0 f
  OnPos _ f = 'There 0

type family CountPar p where
  CountPar Par1 = 1
  CountPar (K1 i c) = 0
  CountPar (f :.: g) = CountPar g
  CountPar (Rec1 t) = 1

-- >>> :kind! RawFieldOf "a4" (Rep1 Foo)
-- RawFieldOf "a4" (Rep1 Foo) :: GPos
-- = 'Here 3 (Maybe :.: Rec1 [])

instance
  ( l ~~ sym
  , t ~~ u
  , 'Here n g ~~ RawFieldOf l t
  , ga ~~ Flatten g a
  , gb ~~ Flatten g b
  ) =>
  SetField l (Partial t a b '[sym]) (u b) ga gb

type Delete :: forall {k}. k -> k -> k -> [k] -> [k]
type family Delete x y y' ys where
  Delete l l k xs = k ': xs
  Delete l k l xs = k ': xs
  Delete l k k' '[] = '[k, k']
  Delete l k k' (l ': ks) = k ': k' ': ks
  Delete l k k' (k'' ': ks) = k ': Delete l k' k'' ks

instance
  ( ks' ~~ Delete l k k' cs
  , 'Here n g ~~ RawFieldOf l t
  , ga ~~ Flatten g a
  , gb ~~ Flatten g b
  ) =>
  SetField l (Partial t a b (k ': k' ': cs)) (Partial t a b ks') ga gb

type ParFields t = GParFields '[] (Rep1 t)

type family GParFields syms p where
  GParFields syms (M1 S ( 'MetaSel ( 'Just l) _ _ _) f) =
    GParFieldsAux (CountPar f) l syms
  GParFields syms (M1 i ( 'MetaSel ( 'Just l) _ _ _) f) =
    GParFields syms f
  GParFields syms (f :*: g) =
    GParFields (GParFields syms g) f

type family GParFieldsAux n l syms where
  GParFieldsAux 1 l syms = l ': syms
  GParFieldsAux _ _ syms = syms

instance
  ( 'Here n ~~ RawFieldOf l t
  , syms ~ ParFields t
  ) =>
  SetField l (t a) (Partial t a b syms) a b

data Foo a = Foo {a1 :: a, str :: String, a2, a3 :: a, a4 :: Maybe [a]}
  deriving (Show, Eq, Ord, Generic, Generic1)
  deriving (Dissectable) via Generically1 Foo
