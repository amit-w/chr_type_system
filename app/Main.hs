{-# LANGUAGE DataKinds #-}

-- | An end-to-end example of embedding a CHR module in a Haskell program.
--
-- @examples/stlc/stlc.chr@ is a Curry-style simply-typed lambda-calculus
-- type inferencer written in CHR. This driver parses a small surface
-- syntax (see "Parser"), encodes the resulting term into CHR data with the
-- @ToTerm@ instance in "Syntax", runs the @typecheck/2@ goal with
-- 'runQueryCompiled', and
-- decodes the inferred type back into a Haskell 'Type' (or a type error)
-- with 'FromTerm' — the whole round trip goes through "YCHR.Convert".
--
-- With no arguments it is a small type-inference REPL; @--demo@ prints a
-- fixed table:
--
-- > cabal run stlc-typechecker            # REPL
-- > cabal run stlc-typechecker -- --demo  # demo table
module Main (main) where

import Control.Monad (when)
import Control.Exception (throwIO, Exception (..), catch, annotateIO, ExceptionWithContext (ExceptionWithContext))
import Control.Exception.Annotation (ExceptionAnnotation (displayExceptionAnnotation))
import Control.Exception.Context (displayExceptionContext)
import Data.Bifunctor (Bifunctor(first))
import Data.Char (isSpace)

import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.IO
  ( BufferMode (NoBuffering),
    hFlush,
    hIsTerminalDevice,
    hPutStrLn,
    hSetBuffering,
    isEOF,
    stderr,
    stdin,
    stdout,
  )

import YCHR
  ( CompiledProgram,
    compileModules,
  )

import Language.Lambda.Parser (parseExpr)
import Language.Lambda.Typecheck
    ( TryTypedExpr(..),
      TCResult(..),
      Type(..),
      typecheck,
      TypedExpr
    )
import Language.Lambda.Typecheck.Sanity qualified as Sanity

import Embed (ChrSource, newChrSource, readChrSource, stlcPath)
import PrettyPrint
import ReplError (wrapConvertError, ReplError, Phase (..), TCError (..), SanityFailure (..))

-- ---------------------------------------------------------------------------
-- Exceptions
-- ---------------------------------------------------------------------------

newtype ContextExpr = ContextExpr TryTypedExpr
  deriving (Show)

instance ExceptionAnnotation ContextExpr where
  displayExceptionAnnotation (ContextExpr tryExpr) = prefix ++ "annotated expression: " ++ renderTryExpr tryExpr where
    prefix = case tryExpr of {Failed _ -> "(partially) " ; Typed _ -> ""}

newtype ContextType = ContextType Type
  deriving (Show)

instance ExceptionAnnotation ContextType where
  displayExceptionAnnotation (ContextType ty) = renderType False ty

-- Extracted from newer versions of base
data NoBacktrace e = NoBacktrace e
  deriving (Show)

instance Exception e => Exception (NoBacktrace e) where
  fromException = fmap NoBacktrace . fromException
  toException (NoBacktrace e) = toException e
  backtraceDesired _ = False
  

fromRightIO :: Exception e => Either e a -> IO a
fromRightIO (Left e) = throwIO (NoBacktrace e)
fromRightIO (Right a) = pure a

-- ---------------------------------------------------------------------------
-- Driver
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  progName <- getProgName
  args <- getArgs
  chrSource <- loadInferencer stlcPath
  case args of
    [] -> runRepl chrSource
    _ -> hPutStrLn stderr ("usage: " ++ progName) >> exitFailure

-- | Compile the embedded inferencer once; reuse it across every query.
loadInferencer :: FilePath -> IO (ChrSource CompiledProgram)
loadInferencer path =
  newChrSource path $ \source ->do
    (chrSource, _warnings) <- annotateIO PhaseCompileChr $ fromRightIO $ compileModules True [(path, source)]  
    pure chrSource

-- ---------------------------------------------------------------------------
-- REPL
-- ---------------------------------------------------------------------------

runRepl :: ChrSource CompiledProgram -> IO ()
runRepl chrSource = do
  hSetBuffering stdout NoBuffering
  interactive <- hIsTerminalDevice stdin
  when interactive $
    putStrLn "STLC type-inference REPL. Enter a lambda term (e.g. \\x. x + 1); :q to quit."
  loop interactive
  where
    loop interactive = do
      when interactive (putStr "stlc> ")
      hFlush stdout
      atEof <- isEOF
      if atEof
        then when interactive (putStrLn "")
        else do
          line <- getLine
          keepGoing <- step interactive line `catch` handler
          when keepGoing (loop interactive)

    handler (ExceptionWithContext ctxt (err :: ReplError)) = do
      putStrLn "\nerror:"
      putStr (displayExceptionContext ctxt)
      putStrLn (displayException err)
      pure True

    step interactive line
      | command `elem` [":q", ":quit"] = pure False
      | null command = pure True
      | otherwise = do
          when (not interactive) (putStrLn ("stlc> " ++ line))
          cp <- readChrSource chrSource
          e <- annotateIO PhaseParse $ fromRightIO $ parseExpr line
          -- TODO maybe we want to separate encode errors and decode errors, using `runCompiledWith Right`,
          -- (cont.) and handling the decoding in main (or in a function main calls).
          -- (cont.) This will somewhat break an abstraction, but it is already broken with all the TryTypedExpr and such.
          tcResult <- annotateIO PhaseTypeCheck $ typecheck cp e
          (tryTypedExpr, exprTypeOrError) <- annotateIO PhaseDecodeResult $ fromRightIO $ first wrapConvertError $ tcResult
          exprType <- annotateIO (ContextExpr tryTypedExpr) $ fromRightIO (fromTCResult exprTypeOrError)
          putStrLn $ "type: " ++ renderType False exprType
          typedExpr <- annotateIO (ContextType exprType) $ fromRightIO (fromTyped tryTypedExpr)
          putStrLn $ "annotated expr: " ++ renderExpr typedExpr
          annotateIO PhaseSanityTypeCheck $ fromRightIO $ first SanityFailure $ Sanity.check typedExpr exprType
          -- _
          -- putStrLn $ concatMap (('\n' :) . describeSanityTCError) sanityErrs
          -- (typedExpr :: TypedExpr, exprType :: Type) <- annotateIO PhaseDecodeResult {-TODO phase-} $ liftA2 (,) <$> fromRightIO (_ tryTypedExpr) <*> fromRightIO (_ exprTypeOrError)
          pure True
      where
        command = strip line

fromTCResult :: TCResult -> Either TCError Type
fromTCResult (Ok ty) = Right ty
fromTCResult (Ill errs) = Left $ IllTyped errs

fromTyped :: TryTypedExpr -> Either TCError TypedExpr
fromTyped (Typed typed) = Right typed
fromTyped (Failed partlyAnnotated) = Left $ NotFullyAnnotated partlyAnnotated

-- ---------------------------------------------------------------------------
-- Demo table
-- ---------------------------------------------------------------------------

-- NOTE: Not deleting this to remind myself to add tests from these
demoInputs :: [String]
demoInputs =
  [ "\\x. x + 1",
    "\\x. x",
    "(\\x. x + 1) 5",
    "\\x. \\y. x",
    "\\f. \\x. f (f x)",
    "let f = \\x. x + 1 in f 5",
    "\\x. x x",
    "1 2",
    "y"
  ]

-- ---------------------------------------------------------------------------
-- Small helpers
-- ---------------------------------------------------------------------------

strip :: String -> String
strip = f . f where f = reverse . dropWhile isSpace
