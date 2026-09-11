module Render (
    Render,
    restartPrec,
    paren,
    renderString,
    renderText,
    runRender,
    withPrec,
    noAssoc,
) where

import Control.Monad.Reader (MonadReader(local))

import Data.Monoid (Endo (..))
import Data.Text (Text, unpack)
import Data.String (IsString (fromString))

newtype Render = Render (Int -> ShowS)
    deriving (Semigroup, Monoid) via (Int -> Endo String)

restartPrec :: Render -> Render
restartPrec (Render f) = Render $ local (const 0) f

paren :: Render -> Render
paren fa = renderText "(" <> restartPrec fa <> renderText ")"

renderString :: String -> Render
renderString s = Render $ const (s ++) 

instance IsString Render where
  fromString = renderString

renderText :: Text -> Render
renderText = renderString . unpack

runRender :: Render -> String
runRender (Render f) = f 0 ""

_changePrec :: Int -> Render -> Render
_changePrec prec (Render f) = Render $ local (const prec) f

withPrec :: Int -> Render -> Render
withPrec prec (Render f) = Render $ \actualPrec ->
  let inner = f prec in showParen (actualPrec > prec) inner

noAssoc :: Render -> Render
noAssoc (Render f) = Render $ local (+ 1) f
