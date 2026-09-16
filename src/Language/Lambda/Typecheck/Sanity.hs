-- A simple type-checker (no unification) that can verify the output of Language.Lambda.Typecheck
module Language.Lambda.Typecheck.Sanity (Error(..), VarSortMismatch (..), infer, check) where

import Data.Monoid (Endo(..))
import Data.Bifunctor (Bifunctor(first))
import Data.Foldable (traverse_)
import Control.Monad ((>=>), when)

import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.Error.Class (MonadError(throwError))

import Data.Text (Text)

import Data.Validation (Validation, toEither)
import Language.Lambda.Syntax (GenExpr(..))
import Language.Lambda.Typecheck (TypedExpr, Type (..), TypeAnnotations (ArgType))
import Language.Lambda.Typecheck qualified as Typed
import Data.List ((!?))

data VarType
  = Mono Type
  | Poly
    { instLevel :: Int
      -- TODO add type-param count
    , ty :: Type
    }

data Env = Env { vars :: [(Text, VarType)], level :: Int }

data VarSortMismatch = VarIsMono | VarIsPoly
  deriving (Show)

data Error
  = TypeMismatch { expected :: Type, actual :: Type }
  | ExpectedArrow { actual :: Type }
  | NotInScope { varName :: Text }
  | VarSortMismatch Text VarSortMismatch
  | NotEnoughTypeParams Int Int
  deriving (Show)

type M = ReaderT Env (Validation (Endo [Error]))

nestEnv :: M a -> M a
nestEnv = local $ \env -> env{level = env.level + 1}

extendEnv :: Text -> VarType -> M a -> M a
extendEnv varName ty = local $ \env -> env{vars = (varName, ty) : env.vars}

lookupEnv :: Text -> M VarType
lookupEnv varName = asks (\env -> lookup varName env.vars) `orElse` NotInScope {varName}

typeError :: Error -> M a
typeError e = throwError $ Endo (e :)

orElse :: M (Maybe a) -> Error -> M a
orElse ma err = ma >>= maybe (typeError err) pure

runM :: M a -> Either [Error] a
runM ma = first (reverse . flip appEndo mempty) $ toEither $ runReaderT ma initialEnv where
  initialEnv = Env { vars=[] , level=0 }

inst :: Int -> [Type] -> Type -> M Type
inst instLevel typeParams = go where
  go :: Type -> M Type
  go TInt = pure TInt
  go (TArrow argTy resTy) = liftA2 TArrow (go argTy) (go resTy)
  go tvar@(TVar typeVarLevel index)
    | typeVarLevel < instLevel = pure tvar
    | typeVarLevel == instLevel = pure (typeParams !? index) `orElse` NotEnoughTypeParams index (length typeParams)
    | otherwise = error "shouldn't get here"

walk :: TypedExpr -> M Type
walk (Var useSiteAnnot v) = do
  varType <- lookupEnv v
  case (useSiteAnnot, varType) of
    (Typed.Mono, Mono ty) -> pure ty
    (Typed.Poly typeParams, Poly level ty) -> inst level typeParams ty
    (Typed.Mono, Poly _ _) -> typeError $ VarSortMismatch v VarIsPoly
    (Typed.Poly _, Mono _) -> typeError $ VarSortMismatch v VarIsMono
walk (Lam (ArgType argTy) v body) = extendEnv v (Mono argTy) $ fmap (TArrow argTy) $ walk body
walk (App f arg) = do
  ((expectedArgTy, resTy), argTy) <- liftA2 (,) (walk f >>= checkArrow) (walk arg)
  checkEq expectedArgTy argTy
  pure resTy
walk (Let v e1 e2) = do
  (instLevel, ty) <- nestEnv $ liftA2 (,) (asks level) (walk e1)
  extendEnv v (Poly {instLevel, ty}) $ walk e2
walk (IntLit _) = pure TInt
walk (Add l r) = traverse_ (walk >=> checkEq TInt) [l, r] *> pure TInt

infer :: TypedExpr -> Either [Error] Type
infer  = runM . walk

check :: TypedExpr -> Type -> Either [Error] ()
check expr ty = runM $ walk expr >>= checkEq ty 

checkArrow :: Type -> M (Type, Type)
checkArrow (TArrow a b) = pure (a, b)
checkArrow ty = typeError $ ExpectedArrow {actual=ty}

checkEq :: Type -> Type -> M ()
checkEq expected actual = when (expected /= actual) $ typeError TypeMismatch {expected, actual}
