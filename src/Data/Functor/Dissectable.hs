{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

{- |
Implemenation of <Clowns to the Left of me, Jokers to the Right http://strictlypositive.org/CJ.pdf> by Conor McBride,
following its <variant by Sandy Maguire https://reasonablypolymorphic.com/blog/clowns-jokers/index.html>.

We have flipped the role of left and right parameters to make 'Suspended' profunctor, making it seems alike a function.
-}
module Data.Functor.Dissectable
  ( Dissectable (..),
    GDissectable (..),
    Suspended (Done, More),
    Generically1 (..),
    update,
  )
where

import Data.Bifunctor
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Sum
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Void (Void)
import GHC.Generics

data GSusp p k l r where
  GDone :: p r -> GSusp p k l r
  GMore :: l -> k l r -> GSusp p k l r

deriving instance
  ( Show l
  , Show (p r)
  , Show (k l r)
  ) =>
  Show (GSusp p k l r)

newtype Suspended p l r = Suspended (GSusp p (Derivative p) l r)

class Dissectable (f :: Type -> Type) where
  type Derivative f :: Type -> Type -> Type
  start :: f l -> Suspended f l r
  proceed :: r -> Derivative f l r -> Suspended f l r

class GDissectable (f :: Type -> Type) where
  data GDerivative f :: Type -> Type -> Type
  gstart :: f l -> GSusp f (GDerivative f) l r
  gproceed :: r -> GDerivative f l r -> GSusp f (GDerivative f) l r

bihoist ::
  (forall x. f x -> g x) ->
  (forall x y. k x y -> h x y) ->
  GSusp f k a b ->
  GSusp g h a b
bihoist fg _ (GDone fa) = GDone (fg fa)
bihoist _ xy (GMore b gd) = GMore b (xy gd)

instance GDissectable f => GDissectable (M1 i c f) where
  newtype GDerivative (M1 i c f) a b = M1GDeriv {getM1Deriv :: GDerivative f a b}
  gstart = coerce . gstart . unM1
  {-# INLINE gstart #-}
  gproceed fc = coerce . gproceed fc . getM1Deriv
  {-# INLINE gproceed #-}

deriving instance
  Show (GDerivative f a b) =>
  Show (GDerivative (M1 i c f) a b)

newtype Const x a b = Const {getConst :: x}
  deriving (Show, Eq, Ord, Generic, Functor)

instance Bifunctor (Const x) where
  bimap _ _ = coerce
  {-# INLINE bimap #-}

instance GDissectable U1 where
  newtype GDerivative U1 a b = U1GDeriv (Const Void a b)
    deriving (Show)
    deriving stock (Functor)
    deriving newtype (Bifunctor)
  gstart = const $ GDone U1
  {-# INLINE gstart #-}
  gproceed = const $ \case {}
  {-# INLINE gproceed #-}

instance GDissectable V1 where
  newtype GDerivative V1 a b = V1GDeriv (Const Void a b)
    deriving (Show)
    deriving newtype (Bifunctor, Functor)
  gstart = \case {}
  {-# INLINE gstart #-}
  gproceed = const $ \case {}
  {-# INLINE gproceed #-}

instance GDissectable Par1 where
  newtype GDerivative Par1 a b = Par1GDeriv (Const () a b)
    deriving (Show)
    deriving newtype (Bifunctor, Functor)
  gstart = (`GMore` Par1GDeriv (Const ())) . unPar1
  {-# INLINE gstart #-}
  gproceed = const . GDone . Par1
  {-# INLINE gproceed #-}

instance GDissectable (K1 i c) where
  newtype GDerivative (K1 i c) a b = K1GDeriv (Const Void a b)
    deriving (Show)
    deriving newtype (Bifunctor, Functor)
  gstart = GDone . coerce
  {-# INLINE gstart #-}
  gproceed = const $ \case {}
  {-# INLINE gproceed #-}

instance (GDissectable f, GDissectable g) => GDissectable (f :+: g) where
  newtype GDerivative (f :+: g) a b = SumGDeriv ((GDerivative f |+| GDerivative g) a b)
  gstart (L1 fr) = bihoist L1 (SumGDeriv . L2) $ gstart fr
  gstart (R1 gr) = bihoist R1 (SumGDeriv . R2) $ gstart gr
  {-# INLINE gstart #-}
  gproceed c (SumGDeriv (L2 cl)) = bihoist L1 (SumGDeriv . L2) $ gproceed c cl
  gproceed c (SumGDeriv (R2 cl)) = bihoist R1 (SumGDeriv . R2) $ gproceed c cl
  {-# INLINE gproceed #-}

deriving instance
  ( Show (GDerivative f a b)
  , Show (GDerivative g a b)
  ) =>
  Show (GDerivative (f :+: g) a b)

infixl 7 |*|

infixl 6 |+|

type (|*|) l r = Product l r

type (|+|) l r = Sum l r

mindp ::
  GDissectable g =>
  GSusp f (GDerivative f) c j ->
  g c ->
  GSusp (f :*: g) (GDerivative (f :*: g)) c j
mindp (GMore j gd) qj = GMore j $ ProdDeriv $ L2 $ Pair gd (Clown qj)
mindp (GDone fc) qj = mindq fc $ gstart qj

mindq :: f j -> GSusp g (GDerivative g) c j -> GSusp (f :*: g) (GDerivative (f :*: g)) c j
mindq fc (GDone gc) = GDone (fc :*: gc)
mindq fc (GMore j gd) = GMore j $ ProdDeriv $ R2 (Pair (Joker fc) gd)

instance (GDissectable f, GDissectable g) => GDissectable (f :*: g) where
  newtype GDerivative (f :*: g) a b
    = ProdDeriv ((GDerivative f |*| Clown g |+| Joker f |*| GDerivative g) a b)
  gstart (pj :*: qj) = mindp (gstart pj) qj
  {-# INLINE gstart #-}
  gproceed c (ProdDeriv (L2 (Pair pd (Clown qj)))) = mindp (gproceed c pd) qj
  gproceed c (ProdDeriv (R2 (Pair (Joker pc) qd))) = mindq pc (gproceed c qd)
  {-# INLINE gproceed #-}

deriving instance
  ( Show (f b)
  , Show (g a)
  , Show (GDerivative f a b)
  , Show (GDerivative g a b)
  ) =>
  Show (GDerivative (f :*: g) a b)

instance (Dissectable f, GDissectable g) => GDissectable (f :.: g) where
  newtype GDerivative (f :.: g) a b
    = CompGDeriv ((Biff (Derivative f) g g |*| GDerivative g) a b)
  gstart (Comp1 fg0) = case start fg0 of
    Done f -> GDone $ Comp1 f
    More gj gd -> continue gj gd
    where
      continue gj0 gd0 = case gstart gj0 of
        GMore j gd' ->
          GMore j $ CompGDeriv $ Pair (Biff gd0) gd'
        GDone g ->
          case proceed g gd0 of
            More gj gd -> continue gj gd
            Done fg -> GDone $ Comp1 fg
  {-# INLINE gstart #-}
  gproceed c (CompGDeriv (Pair cfg@(Biff fg) gd0)) =
    case gproceed c gd0 of
      GMore j gd -> GMore j $ CompGDeriv $ Pair cfg gd
      GDone gc -> finish gc
    where
      finish gc =
        case proceed gc fg of
          Done f -> GDone $ Comp1 f
          More gj gd ->
            case gstart gj of
              GMore j gd' -> GMore j $ CompGDeriv $ Pair (Biff gd) gd'
              GDone gc' -> finish gc'
  {-# INLINE gproceed #-}

deriving instance
  ( Show (Derivative f (g a) (g b))
  , Show (GDerivative g a b)
  ) =>
  Show (GDerivative (f :.: g) a b)

deriving newtype instance
  (Show l, Show (p r), Show (Derivative p l r)) =>
  Show (Suspended p l r)

pattern Done :: p r -> Suspended p l r
pattern Done pr = Suspended (GDone pr)

pattern More :: l -> Derivative p l r -> Suspended p l r
pattern More l d = Suspended (GMore l d)

{-# COMPLETE Done, More #-}

instance Dissectable f => GDissectable (Rec1 f) where
  newtype GDerivative (Rec1 f) a b = RecGDeriv (Derivative f a b)
  gstart = coerce $ start @f
  {-# INLINE gstart #-}
  gproceed = coerce $ proceed @f
  {-# INLINE gproceed #-}

deriving instance
  Show (Derivative f a b) => Show (GDerivative (Rec1 f) a b)

newtype Generically1 f a = Generically1 {getGenerically1 :: f a}

instance (Generic1 f, GDissectable (Rep1 f)) => Dissectable (Generically1 f) where
  type Derivative (Generically1 f) = GDerivative (Rep1 f)
  start = Suspended . bihoist (Generically1 . to1) id . gstart . from1 . getGenerically1
  {-# INLINE start #-}
  proceed x = Suspended . bihoist (Generically1 . to1) id . gproceed x
  {-# INLINE proceed #-}

deriving via Generically1 [] instance Dissectable []

data Foo a = Foo {a1 :: a, str :: String, a2 :: a}
  deriving (Show, Eq, Ord, Generic, Generic1)
  deriving (Dissectable) via Generically1 Foo

update :: Dissectable f => (a -> b) -> Suspended f a b -> Suspended f a b
update _ (Done r) = Done r
update f (More x rest) = proceed (f x) rest

-- >>> update show $ update show $ start $ Foo (42 :: Int) "hehe" 5
-- GDone (Foo {a1 = "42", str = "hehe", a2 = "5"})
