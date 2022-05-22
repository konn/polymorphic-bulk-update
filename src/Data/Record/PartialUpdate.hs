{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Data.Record.PartialUpdate where

import Data.Functor.Dissectable
import GHC.Generics
import GHC.TypeLits (Symbol)

newtype Updating (allFields :: [Symbol]) (rest :: [Symbol]) f a b
  = Updating (Suspended f a b)
