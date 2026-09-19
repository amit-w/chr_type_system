module ChrSource
  ( ChrSource
  , newChrSource
  , readChrSource
  )
where

import Control.Monad (when)
import Control.Monad.Writer (WriterT (..), lift, tell)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Monoid (Any (..))
import Data.Text (Text)
import Data.Text.IO qualified as TIO

import System.Posix (EpochTime, getFileStatus, modificationTime)

import YCHR (CompiledProgram, compileModules)
import YCHR.Internal.Compile.Pipeline qualified as Pipeline

data LazyFile
  = LazyFile
  { path :: FilePath,
    timestamp :: IORef EpochTime,
    content :: IORef Text
  }

newLazyFile :: FilePath -> IO LazyFile
newLazyFile path = do
  timestamp <- newIORef . modificationTime =<< getFileStatus path
  content <- newIORef =<< TIO.readFile path
  pure $ LazyFile {path, timestamp, content}

updateLazyFile :: LazyFile -> EpochTime -> IO Text
updateLazyFile lazyFile fileTimeStamp = do
  content <- TIO.readFile lazyFile.path
  writeIORef lazyFile.content content
  writeIORef lazyFile.timestamp fileTimeStamp
  pure content

readLazyFile :: LazyFile -> WriterT Any IO Text
readLazyFile lazyFile = do
  fileTimeStamp <- lift $ modificationTime <$> getFileStatus lazyFile.path
  storedTimeStamp <- lift $ readIORef lazyFile.timestamp
  if storedTimeStamp >= fileTimeStamp
    then lift (readIORef lazyFile.content)
    else tellUpdated *> lift (updateLazyFile lazyFile fileTimeStamp)

tellUpdated :: WriterT Any IO ()
tellUpdated = tell (Any True)

type Result = Either Pipeline.Error CompiledProgram

data ChrSource
  = ChrSource
  { files :: [LazyFile],
    value :: IORef Result
  }

newChrSource :: [FilePath] -> IO ChrSource
newChrSource paths = do
  files <- traverse newLazyFile paths
  value <- newIORef =<< loaderFunc <$> traverse (\lazyFile -> (lazyFile.path,) <$> readIORef lazyFile.content) files
  pure $ ChrSource {files, value}

loaderFunc :: [(FilePath, Text)] -> Either Pipeline.Error CompiledProgram
loaderFunc = fmap fst . compileModules True

readChrSource :: ChrSource -> IO Result
readChrSource chrSource = do
  (contents, Any anyChanged) <- runWriterT $ traverse (\lazyFile -> (lazyFile.path,) <$> readLazyFile lazyFile) chrSource.files
  when anyChanged $ do
    writeIORef chrSource.value $ loaderFunc contents
  readIORef chrSource.value
