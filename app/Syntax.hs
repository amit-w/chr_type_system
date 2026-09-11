{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | The object language shared by the parser and the driver. Kept in its
-- own module so "Parser" and "Main" can both import it without a cycle;
-- the 'ToTerm' instance lives here too (with the type it encodes) so it is
-- not an orphan.
module Syntax
  ( GenExpr (..),
    Loc (..),
    SLoc (..),
  )
where

import Data.Functor.Const (Const (..))
import Data.Singletons (Sing, SingI (sing))
import Data.Text (Text)
import GHC.Generics (Generic1)
import HFunctor (Apply (getApply), HFoldable, HFunctor, HTraversable)
import YCHR (ToTerm (..), compound)

data Loc = LocVar | LocLam

data SLoc (l :: Loc) where
  SLocVar :: SLoc LocVar
  SLocLam :: SLoc LocLam

type instance Sing = SLoc

instance SingI LocVar where
  sing = SLocVar

instance SingI LocLam where
  sing = SLocLam

-- | Unannotated lambda terms. @let x = e1 in e2@ is desugared by the
-- parser to @(\\x. e2) e1@, so it needs no constructor of its own.
data GenExpr f
  = Var (Apply LocVar f) Text
  | Lam (Apply LocLam f) Text (GenExpr f)
  | App (GenExpr f) (GenExpr f)
  | Let Text (GenExpr f) (GenExpr f)
  | IntLit Integer
  | Add (GenExpr f) (GenExpr f)
  deriving (Generic1)

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
  toTerm (Var annot x) = compound "evar" [toTerm x, toTerm annot.getApply.getConst]
  toTerm (Lam ty x body) = compound "lam" [toTerm x, toTerm ty.getApply.getConst, toTerm body]
  toTerm (App f a) = compound "app" [toTerm f, toTerm a]
  toTerm (Let x a e) = compound "let" [toTerm x, toTerm a, toTerm e]
  toTerm (IntLit n) = compound "lit_int" [toTerm n]
  toTerm (Add a b) = compound "add" [toTerm a, toTerm b]
