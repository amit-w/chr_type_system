{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}

module Data.HTraversable (HTraversable (..)) where

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

import Data.HFunctor (HFunctor)
import Data.HFoldable (HFoldable)

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
