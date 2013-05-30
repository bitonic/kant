module Kant.Prelude (preludeFile) where

import           System.FilePath ((</>))
import           Control.Monad.Trans (MonadIO(..))

import           Kant.Common
import           Paths_kant

preludeFile :: MonadIO m => m FilePath
preludeFile = liftIO ((</> "prelude.ka") <$> getDataDir)
