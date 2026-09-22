module PrettyPrint (
  renderType,
  renderTypeTerm,
  describeSanityTCError,
  describeError,
  renderExpr,
  viewTerm,
)
where

import Data.List (intercalate)

import Data.Text (Text)
import Data.Text qualified as T

import YCHR (
  Name (..),
  Term (..),
 )

import Language.Lambda.Syntax (GenExpr (..))
import Language.Lambda.Typecheck (
  Type (..),
  TypeAnnotations (ArgType, Mono, Poly),
 )
import Language.Lambda.Typecheck.Sanity qualified as Sanity

import Render (
  noAssoc,
  paren,
  renderString,
  renderText,
  restartPrec,
  runRender,
  withPrec,
 )

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

describeSanityTCError :: Sanity.Error -> String
describeSanityTCError Sanity.TypeMismatch{Sanity.expected, Sanity.actual} =
  mconcat
    [ "expected: "
    , renderType False expected
    , ", found: "
    , renderType False actual
    , "."
    ]
describeSanityTCError Sanity.ExpectedArrow{Sanity.actual} =
  mconcat
    [ "expected a function type, found: "
    , renderType False actual
    , "."
    ]
describeSanityTCError Sanity.NotInScope{Sanity.varName} =
  mconcat
    [ "not in scope: "
    , T.unpack varName
    ]
describeSanityTCError (Sanity.VarSortMismatch varName mismatchKind) =
  mconcat
    [ "var sort mismatch in "
    , T.unpack varName
    , ". var is: "
    , expected
    , ", used as: "
    , actual
    , "."
    ]
 where
  (expected, actual) = case mismatchKind of
    Sanity.VarIsMono -> ("mono", "poly")
    Sanity.VarIsPoly -> ("poly", "mono")
describeSanityTCError (Sanity.NotEnoughTypeParams index len) =
  mconcat
    [ "not enough type parameters. accessed index "
    , show index
    , ", while there are only "
    , show len
    , " type parameters."
    ]

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
  _ -> "unparsed error: " ++ viewTerm t

renderExpr :: GenExpr TypeAnnotations -> String
renderExpr expr = runRender (go expr)
 where
  go (Lam (ArgType ty) v e) =
    withPrec 1 $
      mconcat
        [ "\\"
        , paren $ mconcat [renderText v, ": ", renderString (renderType False ty)]
        , ". "
        , go e
        ]
  go (App l r) = withPrec 7 $ go l <> " " <> noAssoc (go r)
  go (Var Mono v) = renderText v
  go (Var (Poly ts) v) =
    mconcat
      [ renderText v
      , " @"
      , paren (foldMap (renderString . renderType True <> renderString . const " ") ts)
      ]
  go (Let v e1 e2) =
    withPrec 2 $
      mconcat
        [ "let "
        , renderText v
        , " = "
        , restartPrec (go e1)
        , " in "
        , go e2
        ]
  go (IntLit n) = renderString $ show n
  go (Add l r) = withPrec 3 $ go l <> " + " <> go r

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

viewName :: Name -> String
viewName (Qualified modName name) = T.unpack modName ++ ":" ++ T.unpack name
viewName (Unqualified name) = T.unpack name

viewTerm :: Term -> String
viewTerm (VarTerm name) = T.unpack name
viewTerm (IntTerm n) = show n
viewTerm (FloatTerm n) = show n
viewTerm (TextTerm s) = show s
viewTerm (CompoundTerm name []) = viewName name
viewTerm (CompoundTerm name xs) = viewName name ++ "(" ++ intercalate ", " (map viewTerm xs) ++ ")"
viewTerm Wildcard = "_"