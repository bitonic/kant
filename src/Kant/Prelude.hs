-- | Functions referring to the prelude file and its definitions.
module Kant.Prelude
    ( preludeFile
    , unit
    , tt
    , empty
    , absurd
    ) where

import           System.FilePath ((</>))
import           Control.Monad.Trans (MonadIO(..))

import           Kant.Common
import           Kant.Term
import           Paths_kant

preludeFile :: MonadIO m => m FilePath
preludeFile = liftIO ((</> "prelude.ka") <$> getDataDir)

unit :: ConId
unit = "prelude_Unit"

tt :: ConId
tt = "prelude_tt"

empty :: ConId
empty = "prelude_Empty"

absurd :: ConId
absurd = "prelude_absurd"
