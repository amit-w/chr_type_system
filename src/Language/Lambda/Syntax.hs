{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The object language shared by the parser and the driver. Kept in its
-- own module so "Parser" and "Main" can both import it without a cycle;
-- the 'ToTerm' instance lives here too (with the type it encodes) so it is
-- not an orphan.
module Language.Lambda.Syntax
  ( GenExpr (App, Let, IntLit, Add, Var, Lam),
    Loc (..),
    SLoc (..),
  )
where

import Data.Functor.Const (Const (..))
import GHC.Generics (Generic1)

import Data.Singletons (Sing, SingI (sing))
import Data.Text (Text)

import YCHR (ToTerm (..), compound)

import Data.HFunctor (HFunctor (..))
import Data.HFoldable (HFoldable (..))
import Data.HTraversable (HTraversable (..))

data Loc = LocVar | LocLam

data SLoc (l :: Loc) where
  SLocVar :: SLoc LocVar
  SLocLam :: SLoc LocLam

type instance Sing = SLoc

instance SingI LocVar where
  sing = SLocVar

instance SingI LocLam where
  sing = SLocLam


-- HACK: including (f loc) directly in GenExpr will prevent it from being Generic1, so we use this instead
data Apply (l :: Loc) f = Apply { getApply :: f l }
  deriving (Eq, Show)

instance (SingI x) => HFunctor (Apply x) where
  hmap f (Apply a) = Apply $ f a

instance (SingI x) => HFoldable (Apply x) where
  hfoldMap f (Apply a) = f a

instance (SingI x) => HTraversable (Apply x) where
  htraverse f (Apply a) = Apply <$> f a


-- | Unannotated lambda terms. @let x = e1 in e2@ is desugared by the
-- parser to @(\\x. e2) e1@, so it needs no constructor of its own.
data GenExpr f
  = VarA (Apply LocVar f) Text
  | LamA (Apply LocLam f) Text (GenExpr f)
  | App (GenExpr f) (GenExpr f)
  | Let Text (GenExpr f) (GenExpr f)
  | IntLit Integer
  | Add (GenExpr f) (GenExpr f)
  deriving (Generic1)

{-# COMPLETE Var, Lam, App, Let, IntLit, Add #-}
pattern Var :: f LocVar -> Text -> GenExpr f
pattern Var varAnnot name = VarA (Apply varAnnot) name

pattern Lam :: f LocLam -> Text -> GenExpr f -> GenExpr f
pattern Lam argType argName body = LamA (Apply argType) argName body

deriving instance (Eq a) => Eq (GenExpr (Const a))
deriving instance (Show a) => Show (GenExpr (Const a))
instance (HFunctor GenExpr)
instance (HFoldable GenExpr)
instance (HTraversable GenExpr)

-- | Encode a term as the CHR data the inferencer matches on. These are
-- plain compounds (@evar@, @lam@, …). The inferencer declares and exports
-- them as the @expr@ type, so the goal-building step canonicalizes each
-- one to its qualified form (@stlc:evar@, …) and it reaches the rules as
-- data.
instance (ToTerm a) => ToTerm (GenExpr (Const a)) where
  toTerm (Var annot x) = compound "evar" [toTerm x, toTerm annot.getConst]
  toTerm (Lam ty x body) = compound "lam" [toTerm x, toTerm ty.getConst, toTerm body]
  toTerm (App f a) = compound "app" [toTerm f, toTerm a]
  toTerm (Let x a e) = compound "let" [toTerm x, toTerm a, toTerm e]
  toTerm (IntLit n) = compound "lit_int" [toTerm n]
  toTerm (Add a b) = compound "add" [toTerm a, toTerm b]
