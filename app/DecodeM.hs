{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedRecordDot #-}

module DecodeM (
  DecodeM,
  decodeVarM,
  decodeSumM,
  argAtM,
  orElse,
) where

import Data.Text (Text)
import Data.Map (Map)

import YCHR
  ( FromTerm (..),
    Term (..),
    argAt,
    decodeSum,
    decodeVar,
  )
import YCHR.Convert (ConvertError)
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.Except (catchError)

type DecodeM = ReaderT (Map Text Term) (Either ConvertError)

decodeVarM :: (FromTerm a) => Text -> DecodeM a
decodeVarM varName = ReaderT $ \varMap -> decodeVar varName varMap

decodeSumM :: [(Text, Int, [Term] -> DecodeM a)] -> Term -> DecodeM a
decodeSumM alts term =
  ReaderT $ \varMap -> decodeSum (map (\(a, b, f) -> (a, b, (\k -> k.runReaderT varMap) . f)) alts) term

argAtM :: (FromTerm a) => Int -> [Term] -> DecodeM a
argAtM n as = ReaderT $ const (argAt n as)

orElse :: DecodeM a -> DecodeM a -> DecodeM a
orElse l r = l `catchError` const r