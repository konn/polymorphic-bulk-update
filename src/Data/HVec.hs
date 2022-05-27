{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Data.HVec (HVec) where

import Data.Kind (Type)
import Data.Primitive.SmallArray
import GHC.Exts (Any)

-- TODO: consider exploiting linearity to avoid reallocation
type HVec :: forall {k}. (k -> Type) -> [k] -> Type
newtype HVec h xs = MkHVec (SmallArray Any)
