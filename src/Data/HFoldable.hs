{-# LANGUAGE DataKinds #-}

module Data.HFoldable (HFoldable (..)) where

import Data.Kind (Type)
import Data.Singletons (SingI (..))
import GHC.Generics (
  Generic1 (Rep1, from1),
  K1 (K1),
  M1 (M1),
  Rec1 (Rec1),
  type (:*:) (..),
  type (:+:) (..),
 )

-- HFoldable
class HFoldable (t :: (k -> Type) -> Type) where
  hfoldMap :: (Monoid m) => (forall x. (SingI x) => f x -> m) -> t f -> m
  default hfoldMap :: (Generic1 t, HFoldable (Rep1 t)) => (Monoid m) => (forall x. (SingI x) => f x -> m) -> t f -> m
  hfoldMap f = hfoldMap f . from1

instance (HFoldable h) => HFoldable (M1 i c h) where
  hfoldMap f (M1 a) = hfoldMap f a

instance (HFoldable f, HFoldable g) => HFoldable (f :+: g) where
  hfoldMap f (L1 a) = hfoldMap f a
  hfoldMap f (R1 a) = hfoldMap f a

instance (HFoldable f, HFoldable g) => HFoldable (f :*: g) where
  hfoldMap f (a :*: b) = hfoldMap f a <> hfoldMap f b

instance HFoldable (K1 i c) where
  hfoldMap _ (K1 _) = mempty

instance (HFoldable t) => HFoldable (Rec1 t) where
  hfoldMap f (Rec1 a) = hfoldMap f a
