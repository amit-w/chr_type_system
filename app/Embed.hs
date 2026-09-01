{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Embed
  ( stlcPath
  , ChrSource
  , newChrSource
  , readChrSource
  )
where

import Control.Monad (when)

import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Text (Text)
import Data.Text.IO qualified as TIO

import System.Posix (getFileStatus, modificationTime, EpochTime)

data ChrSource a
  = ChrSource
  { path :: FilePath
  , f :: Text -> IO a
  , timestamp :: IORef EpochTime
  , value :: IORef a
  }

newChrSource :: FilePath -> (Text -> IO a) -> IO (ChrSource a)
newChrSource path f = do
  timestamp <- newIORef . modificationTime =<< getFileStatus path
  value <- newIORef =<< f =<< TIO.readFile path
  pure $ ChrSource {path, f, timestamp, value}

readChrSource :: ChrSource a -> IO a
readChrSource chrSource = do
  fileTimeStamp <- modificationTime <$> getFileStatus chrSource.path
  storedTimeStamp <- readIORef chrSource.timestamp
  when (fileTimeStamp > storedTimeStamp) $ do
    writeIORef chrSource.timestamp fileTimeStamp
    writeIORef chrSource.value =<< chrSource.f =<< TIO.readFile chrSource.path
  readIORef chrSource.value

-- | Path of the inferencer source, relative to the package root (GHC runs
-- splices with the cabal package directory as cwd). Also surfaced in
-- compile diagnostics.
stlcPath :: FilePath
stlcPath = "app/stlc.chr"
