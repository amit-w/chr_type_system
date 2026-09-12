{-# LANGUAGE DataKinds #-}

module Language.Lambda.Typecheck (
  Type(..),
  TCResult(..),
  TypedExpr,
  TryTypedExpr (..),
  typecheck,
  TypeAnnotations(..),
  ) where

import Control.Monad.State (evalState, State, modify, MonadState (get))
import Control.Monad.Reader (ReaderT(runReaderT))
import Data.Functor.Const (Const (..))

import Data.Text (Text, pack)
import Data.Singletons (SingI (..))

import YCHR
  ( CompiledProgram,
    FromTerm (..),
    Term (..),
    ToTerm,
    argAt,
    compound,
    decodeSum,
    runQueryCompiledWith,
    toTerm,
    ConvertError,
  )

import Data.HTraversable (HTraversable (htraverse))

import YCHR.Convert.DecodeM ( DecodeM, decodeVarM, decodeSumM, argAtM, orElse )

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

numberExpr :: Expr -> NumberedExpr
numberExpr e = evalState (htraverse (const freshVariable) e) 0 where
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
  deriving (Eq)

-- | Decode a @ty@ term. The functor is matched on its local name, so the
-- module-qualified @stlc:arrow@ that comes back still decodes.
instance FromTerm Type where
  fromTerm =
    decodeSum
      [ ("tint", 0, \_ -> Right TInt),
        ("arrow", 2, \as -> TArrow <$> argAt 0 as <*> argAt 1 as),
        ("tvar", 2, \as -> TVar <$> argAt 0 as <*> argAt 1 as)
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
      [ ("ok", 1, \as -> Ok <$> argAt 0 as),
        ("type_error", 1, \as -> Ill <$> argAt 0 as)
      ]

data family TypeAnnotations (loc :: Loc)
newtype instance TypeAnnotations LocLam = ArgType { getType :: Type }
data instance TypeAnnotations LocVar = Mono | Poly [Type]

type TypedExpr = GenExpr TypeAnnotations

data TryTypedExpr
  = Typed TypedExpr
  | Failed (GenExpr (Const Term))

-- ---------------------------------------------------------------------------
-- typechecking
-- ---------------------------------------------------------------------------

-- This is the only function exported from this module
typecheck :: CompiledProgram -> Expr -> IO (Either ConvertError (TryTypedExpr, TCResult))
typecheck cp e =
  let e' = numberExpr e
  in runQueryCompiledWith cp (typecheckGoal e') (decodeResult e').runReaderT

decodeChrVar :: FromTerm a => Const ChrVar x -> DecodeM a
decodeChrVar chrVar = decodeVarM chrVar.getConst.varName

decodeResult :: NumberedExpr -> DecodeM (TryTypedExpr, TCResult)
decodeResult e = liftA2 (,) (typedExpr `orElse` failedTypedExpr) (decodeVarM "Result")
  where
    typedExpr = Typed <$> htraverse decodeAnnotation e
    failedTypedExpr = Failed <$> htraverse (\var -> Const <$> decodeChrVar var) e

decodeAnnotation :: forall x. (SingI x) => Const ChrVar x -> DecodeM (TypeAnnotations x)
decodeAnnotation chrVar = case sing @x of
  SLocVar -> do
    term <- decodeChrVar chrVar
    decodeSumM
      [ ("mono_var", 0, const (pure Mono)),
        ("poly_var", 1, \as -> fmap Poly (argAtM 0 as))
      ] term
  SLocLam -> ArgType <$> decodeChrVar chrVar

-- | Build the goal @typecheck(<expr>, Result)@. The encoded expression
-- needs no quoting: @expr@ is a declared, exported type, so the goal's
-- bare @evar@ \/ @lam@ \/ ... references are canonicalized to
-- @stlc:evar@, @stlc:lam@, ... — the same form the rule heads match,
-- and data rather than function calls.
typecheckGoal :: NumberedExpr -> Term
typecheckGoal e = compound "typecheck" [toTerm e, VarTerm "Result"]
