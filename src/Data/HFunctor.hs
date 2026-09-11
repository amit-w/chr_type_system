{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}

module Data.HFunctor (HFunctor (..)) where

import Data.Kind (Type)
import Data.Singletons (SingI (..))
import GHC.Generics
  ( Generic1 (Rep1, from1, to1),
    K1 (K1),
    M1 (M1),
    Rec1 (Rec1),
    type (:*:) (..),
    type (:+:) (..),
  )

-- HFunctor
class HFunctor (t :: (k -> Type) -> Type) where
  hmap :: (forall x. SingI x => f x -> g x) -> t f -> t g
  default hmap :: (Generic1 t, HFunctor (Rep1 t)) => (forall x. SingI x => f x -> g x) -> t f -> t g
  hmap f = to1 . hmap f . from1

instance (HFunctor h) => HFunctor (M1 i c h) where
  hmap f (M1 a) = M1 $ hmap f a

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
  hmap f (L1 a) = L1 $ hmap f a
  hmap f (R1 a) = R1 $ hmap f a

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
  hmap f (a :*: b) = hmap f a :*: hmap f b

instance HFunctor (K1 i c) where
  hmap _ (K1 a) = K1 a

instance (HFunctor t) => HFunctor (Rec1 t) where
  hmap f (Rec1 a) = Rec1 $ hmap f a
