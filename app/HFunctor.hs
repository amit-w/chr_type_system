{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}

module HFunctor where

import Data.Kind (Type)
import Data.Singletons (SingI (..))
import GHC.Generics
  ( K1 (K1),
    M1 (M1),
    Rec1 (Rec1),
    type (:*:) (..),
    type (:+:) (..), Generic1 (from1, to1, Rep1), 
  )

-- Apply
data Apply x f = Apply { getApply :: f x }

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

instance (SingI x) => HFunctor (Apply x) where
  hmap f (Apply a) = Apply $ f a

-- HFoldable
class HFoldable (t :: (k -> Type) -> Type) where
  hfoldMap :: Monoid m => (forall x. SingI x => f x -> m) -> t f -> m
  default hfoldMap :: (Generic1 t, HFoldable (Rep1 t)) => Monoid m => (forall x. SingI x => f x -> m) -> t f -> m
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

instance (SingI x) => HFoldable (Apply x) where
  hfoldMap f (Apply a) = f a

-- HTraversable
class (HFunctor t, HFoldable t) => HTraversable (t :: (k -> Type) -> Type) where
  htraverse :: Applicative m => (forall x. SingI x => f x -> m (g x)) -> t f -> m (t g)
  default htraverse :: (Generic1 t, HTraversable (Rep1 t)) => Applicative m => (forall x. SingI x => f x -> m (g x)) -> t f -> m (t g)
  htraverse f a = fmap to1 . htraverse f . from1 $ a

instance (HTraversable h) => HTraversable (M1 i c h) where
  htraverse f (M1 a) = M1 <$> htraverse f a

instance (HTraversable f, HTraversable g) => HTraversable (f :+: g) where
  htraverse f (L1 a) = L1 <$> htraverse f a
  htraverse f (R1 a) = R1 <$> htraverse f a

instance (HTraversable f, HTraversable g) => HTraversable (f :*: g) where
  htraverse f (a :*: b) = liftA2 (:*:) (htraverse f a) (htraverse f b)

instance HTraversable (K1 i c) where
  htraverse _ (K1 a) = pure $ K1 a

instance (HTraversable t) => HTraversable (Rec1 t) where
  htraverse f (Rec1 a) = Rec1 <$> htraverse f a

instance (SingI x) => HTraversable (Apply x) where
  htraverse f (Apply a) = Apply <$> f a
