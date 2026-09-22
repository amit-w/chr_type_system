module ReplError (
  wrapConvertError,
  ReplError,
  TCError (..),
  SanityFailure (..),
  Phase (..),
)
where

import Control.Applicative (Alternative (..), (<|>))
import Control.Exception (Exception (..), SomeException)
import Control.Exception.Annotation (ExceptionAnnotation (..))
import Control.Monad.Reader (ReaderT (..))
import Data.Functor.Const (Const)

import YCHR (ConvertError, Term)
import YCHR qualified

import Language.Lambda.Parser (ParseError)
import Language.Lambda.Syntax (GenExpr)
import Language.Lambda.Typecheck.Sanity qualified as Sanity

import PrettyPrint (describeError, describeSanityTCError)

newtype WrappedConvertError = WrappedConvertError {unwrap :: ConvertError}
  deriving (Show)

data Phase
  = PhaseCompileChr
  | PhaseParse
  | PhaseEncodeGoal
  | PhaseEmbed
  | PhaseDecodeResult
  | PhaseTypeCheck
  | PhaseSanityTypeCheck
  deriving (Show)

instance ExceptionAnnotation Phase where
  displayExceptionAnnotation phase = "in phase " ++ name ++ ":"
   where
    name = case phase of
      PhaseCompileChr -> "compile chr"
      PhaseParse -> "parse"
      PhaseEncodeGoal -> "encode goal"
      PhaseEmbed -> "embed chr program"
      PhaseDecodeResult -> "decode result"
      PhaseTypeCheck -> "type check"
      PhaseSanityTypeCheck -> "sanity type check"

wrapConvertError :: ConvertError -> WrappedConvertError
wrapConvertError = WrappedConvertError

instance Exception WrappedConvertError

data ReplError
  = ConvertError ConvertError
  | ChrError YCHR.Error
  | ParseError ParseError
  | TCError TCError
  | SanityErrors SanityFailure
  deriving (Show)

data TCError
  = NotFullyAnnotated (GenExpr (Const Term))
  | IllTyped [Term]
  deriving (Show)

instance Exception TCError where
  displayException (NotFullyAnnotated term) = "not fully annotated: " ++ show term
  displayException (IllTyped errs) = unlines ("type errors:" : map describeError errs)

newtype SanityFailure = SanityFailure [Sanity.Error]
  deriving (Show)

instance Exception SanityFailure where
  displayException (SanityFailure errs) = unlines $ map describeSanityTCError errs

embed :: (Exception e) => (e -> a) -> ReaderT SomeException Maybe a
embed f = ReaderT $ fmap f . fromException

instance Exception ReplError where
  fromException =
    runReaderT $
      embed (ConvertError . unwrap)
        <|> embed ChrError
        <|> embed ParseError
        <|> embed TCError
        <|> embed SanityErrors
  displayException (ConvertError err) = show err
  displayException (ChrError err) = YCHR.displayError err
  displayException (ParseError err) = show err
  displayException (TCError err) = displayException err
  displayException (SanityErrors err) = displayException err
