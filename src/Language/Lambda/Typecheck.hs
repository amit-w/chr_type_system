{-# LANGUAGE DataKinds #-}

module Language.Lambda.Typecheck (
  Type (..),
  TypeAnnotations (..),
  TypedExpr,
  RawTypedExpr,
  typecheck,
  numberExpr,
  typecheckGoal,
  decodeTypedExpr,
) where

import Control.Monad.State (MonadState (get), State, evalState, modify)
import Data.Coerce (coerce)
import Data.Functor.Const (Const (..))
import Data.Map (Map, findWithDefault)
import Data.Singletons (SingI (..))

import Data.Text (Text, pack)

import YCHR (
  CompiledProgram,
  ConvertError,
  FromTerm (..),
  Term (..),
  ToTerm,
  argAt,
  compound,
  decodeSum,
  runQueryCompiledWith,
  toTerm,
 )

import Data.HFunctor (HFunctor (hmap))
import Data.HTraversable (HTraversable (htraverse))
import Language.Lambda.Parser (Expr)
import Language.Lambda.Syntax (GenExpr (..), Loc (..), SLoc (..))

-- ---------------------------------------------------------------------------
-- Input to the .chr program
-- ---------------------------------------------------------------------------

newtype ChrVar = ChrVar {varName :: Text}
  deriving (Eq, Show)

instance ToTerm ChrVar where
  toTerm v = VarTerm v.varName

type NumberedExpr = GenExpr (Const ChrVar)

type RawTypedExpr = GenExpr (Const Term)

numberExpr :: Expr -> NumberedExpr
numberExpr e = evalState (htraverse (const freshVariable) e) 0
 where
  freshVariable :: State Int (Const ChrVar x)
  freshVariable = do
    modify (+ 1)
    Const . ChrVar . indexToVarName <$> get

  indexToVarName :: Int -> Text
  indexToVarName = ("Var" <>) . pack . show

-- ---------------------------------------------------------------------------
-- Output of the .chr program
-- ---------------------------------------------------------------------------

data Type
  = TInt
  | TArrow Type Type
  | TVar Int Int
  deriving (Eq, Show)

-- | Decode a @ty@ term. The functor is matched on its local name, so the
-- module-qualified @stlc:arrow@ that comes back still decodes.
instance FromTerm Type where
  fromTerm =
    decodeSum
      [ ("tint", 0, \_ -> Right TInt)
      , ("arrow", 2, \as -> TArrow <$> argAt 0 as <*> argAt 1 as)
      , ("tvar", 2, \as -> TVar <$> argAt 0 as <*> argAt 1 as)
      ]

-- | The inferencer answers with @ok(Type)@ or @type_error(Errors)@. The
-- error list is kept as raw 'Term's (they mention pre-generalization type
-- variables that would not decode as a ground 'Type') and rendered below.
data TCResult
  = Ok Type
  | Ill [Term]

instance FromTerm TCResult where
  fromTerm =
    decodeSum
      [ ("ok", 1, \as -> Ok <$> argAt 0 as)
      , ("type_error", 1, \as -> Ill <$> argAt 0 as)
      ]

data family TypeAnnotations (loc :: Loc)
newtype instance TypeAnnotations LocLam = ArgType {getType :: Type}
  deriving (Show)
data instance TypeAnnotations LocVar = Mono | Poly [Type]
  deriving (Show)

type TypedExpr = GenExpr TypeAnnotations

data TryTypedExpr
  = Typed TypedExpr
  | Failed (GenExpr (Const Term))
  deriving (Show)

-- ---------------------------------------------------------------------------
-- typechecking
-- ---------------------------------------------------------------------------

typecheck :: CompiledProgram -> Term -> NumberedExpr -> IO (Either ConvertError (GenExpr (Const Term), Term, Term))
typecheck cp goal expr = runQueryCompiledWith cp goal (Right . decodeResult expr)

-- TODO (rename): `decode` is used in this module for two quite different things.
decodeResult :: NumberedExpr -> Map Text Term -> (GenExpr (Const Term), Term, Term)
decodeResult e varMap = (typedExpr, exprType, errors)
 where
  typedExpr = hmap (coerce getVar) e
  exprType = getVar "Type"
  errors = getVar "Errors"
  getVar varName = findWithDefault (VarTerm varName) varName varMap

decodeTypedExpr :: RawTypedExpr -> Either ConvertError TypedExpr
decodeTypedExpr = htraverse (coerce decodeAnnotation)

decodeAnnotation :: forall x. (SingI x) => Term -> Either ConvertError (TypeAnnotations x)
decodeAnnotation term = case sing @x of
  SLocVar -> do
    decodeSum
      [ ("mono_var", 0, const (pure Mono))
      , ("poly_var", 1, \as -> fmap Poly (argAt 0 as))
      ]
      term
  SLocLam -> ArgType <$> fromTerm term

-- | Build the goal @typecheck(<expr>, Result)@. The encoded expression
-- needs no quoting: @expr@ is a declared, exported type, so the goal's
-- bare @evar@ \/ @lam@ \/ ... references are canonicalized to
-- @stlc:evar@, @stlc:lam@, ... — the same form the rule heads match,
-- and data rather than function calls.
typecheckGoal :: NumberedExpr -> Term
-- TODO get back errors
typecheckGoal e = compound "typecheck" [toTerm e, VarTerm "Type", VarTerm "Errors"]
