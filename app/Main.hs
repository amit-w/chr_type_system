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
import Data.List (intercalate)

import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.FilePath ((</>))
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

import qualified Data.Text as T

import YCHR
  ( Name (..),
    Term (..),
    FromTerm (fromTerm),
    ConvertError,
  )

import Language.Lambda.Parser (parseExpr)
import Language.Lambda.Typecheck
    ( Type(..),
      RawTypedExpr,
      typecheck,
      numberExpr,
      typecheckGoal,
      decodeTypedExpr,
    )
import Language.Lambda.Typecheck.Sanity qualified as Sanity

import ChrSource (ChrSource, newChrSource, readChrSource)
import PrettyPrint
import ReplError (wrapConvertError, ReplError, Phase (..), SanityFailure (..), TCError (IllTyped))

-- ---------------------------------------------------------------------------
-- Exceptions
-- ---------------------------------------------------------------------------

data ContextExpr = ContextExpr RawTypedExpr Term
  deriving (Show)

instance ExceptionAnnotation ContextExpr where
  displayExceptionAnnotation (ContextExpr rawExpr decodedType) = unlines [
    "partially annotated expression: " ++ show rawExpr,
    "decoded type: " ++ show decodedType
    ]

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
  

throwIONoBacktrace :: Exception e => e -> IO a
throwIONoBacktrace e = throwIO (NoBacktrace e)

fromRightIO :: Exception e => Either e a -> IO a
fromRightIO (Left e) = throwIO (NoBacktrace e)
fromRightIO (Right a) = pure a

runConvertIO :: Either ConvertError a -> IO a
runConvertIO = fromRightIO . first wrapConvertError

-- ---------------------------------------------------------------------------
-- Driver
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  progName <- getProgName
  args <- getArgs
  case args of
    [] -> runRepl =<< newChrSource chrFiles
    _ -> hPutStrLn stderr ("usage: " ++ progName) >> exitFailure

chrFiles :: [FilePath]
chrFiles = map ("chr_files" </>)
  -- types.chr & errors.chr go first, since they have no dependencies,
  -- and no constraints that appear in rule-heads in other modules.
  [ "types.chr"
  , "errors.chr"
  -- generalization_domain.chr goes before other .chr files, to avoid them seeing non-signleton `associate_var`s.
  , "generalization_domain.chr"
  -- The order of the rest of the modules doesn't matter currently.
  , "instantiation_domain.chr"
  , "walk.chr"
  , "typecheck.chr"
  ]

-- ---------------------------------------------------------------------------
-- REPL
-- ---------------------------------------------------------------------------

runRepl :: ChrSource -> IO ()
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
          keepGoing <- step interactive line `catch` (\err -> True <$ handler err)
          when keepGoing (loop interactive)


    step interactive line
      | command `elem` [":q", ":quit"] = pure False
      | null command = pure True
      | otherwise = do
          when (not interactive) (putStrLn ("stlc> " ++ line))
          cp <- annotateIO PhaseCompileChr $ fromRightIO =<< readChrSource chrSource
          e <- annotateIO PhaseParse $ fromRightIO $ parseExpr line
          -- TODO maybe we want to separate encode errors and decode errors, using `runCompiledWith Right`,
          -- (cont.) and handling the decoding in main (or in a function main calls).
          -- (cont.) This will somewhat break an abstraction, but it is already broken with all the TryTypedExpr and such.
          let e' = numberExpr e
          let goal = typecheckGoal e'
          putStrLn $ viewTerm goal
          embededResult <- annotateIO PhaseEmbed $ typecheck cp goal e'
          (rawTypedExpr, rawExprType, rawErrors) <- annotateIO PhaseEncodeGoal $ runConvertIO $ embededResult
          (errors :: [Term]) <- annotateIO PhaseDecodeResult $ runConvertIO $ fromTerm rawErrors
          when (not (null errors)) $ annotateIO PhaseTypeCheck $ throwIONoBacktrace (IllTyped errors)
          (exprType, typedExpr) <- annotateIO PhaseDecodeResult $ do
            exprType <- annotateIO (ContextExpr rawTypedExpr rawExprType) $ runConvertIO $ fromTerm rawExprType
            putStrLn $ "type: " ++ renderType False exprType
            typedExpr <- annotateIO (ContextType exprType) $ runConvertIO $ (decodeTypedExpr rawTypedExpr)
            putStrLn $ "annotated expr: " ++ renderExpr typedExpr
            pure (exprType, typedExpr)
          annotateIO PhaseSanityTypeCheck $ fromRightIO $ first SanityFailure $ Sanity.check typedExpr exprType
          pure True
      where
        command = strip line

handler :: ExceptionWithContext ReplError -> IO ()
handler (ExceptionWithContext ctxt err) = do
  putStrLn "\nerror:"
  putStr (displayExceptionContext ctxt)
  putStrLn (displayException err)

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
