module Data.Validation where
import Control.Monad.Error.Class (MonadError)
import Control.Monad.Except (MonadError(..))

data Validation e a
  = Error e
  | Valid a
  deriving (Functor, Foldable, Traversable)

toEither :: Validation e a -> Either e a
toEither (Error e) = Left e
toEither (Valid a) = Right a

instance Semigroup e => Applicative (Validation e) where
  pure = Valid
  Valid f <*> Valid a = Valid (f a)
  Valid _ <*> Error e = Error e
  Error e <*> Valid _ = Error e
  Error e1 <*> Error e2 = Error (e1 <> e2)

instance Semigroup e => Monad (Validation e) where
  Valid a >>= f = f a
  Error e >>= _ = Error e

instance Semigroup e => MonadError e (Validation e) where
  throwError = Error
  Valid a `catchError`  _ = Valid a
  Error e `catchError` f = f e
