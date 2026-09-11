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

import Control.Monad (forM_, when)
import Data.Char (isSpace)
import Data.List (intercalate)

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

import Data.Text (Text)
import Data.Text qualified as T

import YCHR
  ( CompiledProgram,
    Name (..),
    Term (..),
    compileModules,
    displayError,
  )

import Language.Lambda.Parser (parseExpr)
import Language.Lambda.Syntax (GenExpr (..))
import Language.Lambda.Typecheck
    ( TryTypedExpr(..),
      TypeAnnotations(Poly, ArgType, Mono),
      TCResult(..),
      Type(..),
      typecheck )

import Embed (ChrSource, newChrSource, readChrSource, stlcPath)
import Render
    ( Render,
      restartPrec,
      paren,
      renderString,
      renderText,
      runRender,
      withPrec,
      noAssoc ) 

-- ---------------------------------------------------------------------------
-- Driver
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  progName <- getProgName
  args <- getArgs
  chrSource <- loadInferencer stlcPath
  case args of
    ["--demo"] -> runDemo =<< readChrSource chrSource
    [] -> runRepl chrSource
    _ -> hPutStrLn stderr ("usage: " ++ progName ++ " [--demo]") >> exitFailure

-- | Compile the embedded inferencer once; reuse it across every query.
loadInferencer :: FilePath -> IO (ChrSource CompiledProgram)
loadInferencer path =
  newChrSource path $ \source ->
    case compileModules True [(path, source)] of
      Left err -> fail ("could not compile " ++ stlcPath ++ ":\n" ++ displayError err)
      Right (chrSource, _warnings) -> pure chrSource

-- | Parse, type-check, and render one line of surface syntax.
inferLine :: CompiledProgram -> String -> IO String
inferLine cp line = case parseExpr line of
  Left err -> pure ("parse error: " ++ err)
  Right e -> do
    result <- typecheck cp e
    pure $ case result of
      Left err -> show err
      Right (typedExpr, exprType) -> renderResult exprType ++ "\n" ++ renderTryExpr typedExpr
        

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
          keepGoing <- step interactive line
          when keepGoing (loop interactive)

    step interactive line
      | command `elem` [":q", ":quit"] = pure False
      | null command = pure True
      | otherwise = do
          when (not interactive) (putStrLn ("stlc> " ++ line))
          cp <- readChrSource chrSource
          inferLine cp line >>= putStrLn
          pure True
      where
        command = strip line

-- ---------------------------------------------------------------------------
-- Demo table
-- ---------------------------------------------------------------------------

runDemo :: CompiledProgram -> IO ()
runDemo cp = do
  putStrLn "Curry-style STLC type inference (via a CHR module):\n"
  forM_ demoInputs $ \s -> do
    rendered <- inferLine cp s
    putStrLn (pad 26 s ++ " :  " ++ firstLine rendered)

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
-- Rendering
-- ---------------------------------------------------------------------------

renderResult :: TCResult -> String
renderResult (Ok t) = renderType False t
renderResult (Ill errs) = "TYPE ERROR: " ++ intercalate "; " (map describeError errs)

renderType :: Bool -> Type -> String
renderType _ TInt = "int"
-- This is kinda the worst of all worlds
renderType _ (TVar level n) = tyVarName n ++ "@" ++ show level
renderType shouldParen (TArrow a b) =
  parenthesize shouldParen (renderType True a ++ " -> " ++ renderType False b)

-- | Render a type that is still a raw 'Term' (as it appears inside an
-- error), tolerating the unbound variables an in-progress inference leaves
-- behind.
renderTypeTerm :: Term -> String
renderTypeTerm t = case t of
  CompoundTerm n [] | localName n == "tint" -> "int"
  CompoundTerm n [IntTerm k] | localName n == "tvar" -> tyVarName (fromInteger k)
  CompoundTerm n [a, b]
    | localName n == "arrow" ->
        "(" ++ renderTypeTerm a ++ " -> " ++ renderTypeTerm b ++ ")"
  TextTerm s -> T.unpack s
  -- A type variable still unbound at the point the error was raised.
  VarTerm _ -> "_"
  Wildcard -> "_"
  _ -> "?"

describeError :: Term -> String
describeError t = case t of
  CompoundTerm n [a, b]
    | localName n == "mismatch" ->
        "cannot unify " ++ renderTypeTerm a ++ " with " ++ renderTypeTerm b
  CompoundTerm n [_, ty]
    | localName n == "infinite_type" ->
        "cannot construct the infinite type " ++ renderTypeTerm ty
  CompoundTerm n [x]
    | localName n == "unbound_variable" ->
        "unbound variable " ++ renderTypeTerm x
  -- TODO DELETEME debug code
  CompoundTerm inst_non_var [ty] | inst_non_var == Unqualified "inst_non_var" -> "tried to instantiate a non-var: " ++ renderTypeTerm ty
  CompoundTerm my_error [] | my_error == Unqualified "my_error" -> "my_error"
  CompoundTerm other_error [expr] | other_error == Unqualified "other_error" -> "other_error: " ++ show expr
  _ -> "?"

renderTryExpr :: TryTypedExpr -> String
renderTryExpr (Typed typedExpr) = runRender $ renderExpr typedExpr
renderTryExpr (Failed term) = show term

renderExpr :: GenExpr TypeAnnotations -> Render
renderExpr (Lam (ArgType ty) v e) = withPrec 1 $ mconcat [
    "\\",
    paren $ mconcat [renderText v, ": ", renderString (renderType False ty)],
    ". ",
    renderExpr e
  ]
renderExpr (App l r) = withPrec 7 $ renderExpr l <> " " <> noAssoc (renderExpr r)
renderExpr (Var Mono v) = renderText v
renderExpr (Var (Poly ts) v) = mconcat [
    renderText v,
    " @",
    paren (foldMap (renderString . renderType True) ts)
  ]
renderExpr (Let v e1 e2) = withPrec 2 $ mconcat [
    "let",
    renderText v,
    " = ",
    restartPrec (renderExpr e1),
    " in ",
    renderExpr e2
  ]
renderExpr (IntLit n) = renderString $ show n
renderExpr (Add l r) = withPrec 3 $ renderExpr l <> " + " <> renderExpr r

-- ---------------------------------------------------------------------------
-- Small helpers
-- ---------------------------------------------------------------------------

localName :: Name -> Text
localName (Unqualified n) = n
localName (Qualified _ n) = n

tyVarName :: Int -> String
tyVarName n
  | n < 26 = [toEnum (fromEnum 'a' + n)]
  | otherwise = 't' : show n

parenthesize :: Bool -> String -> String
parenthesize True s = "(" ++ s ++ ")"
parenthesize False s = s

pad :: Int -> String -> String
pad w s = s ++ replicate (max 1 (w - length s)) ' '

strip :: String -> String
strip = f . f where f = reverse . dropWhile isSpace

-- | Collapse a multi-line parse-error message to its first non-empty line
-- so the REPL prints one tidy line.
firstLine :: String -> String
firstLine = unwords . filter (not . null) . map strip . lines
