-- | Functions referring to the prelude file and its definitions.
module Kant.Prelude
    ( preludeFile
    , unit
    , tt
    , empty
    , absurd
    , and
    , pair
    , fst
    , snd
    ) where

import           Control.Monad.Trans (MonadIO(..))
import           Prelude (Monad(..))
import           System.FilePath ((</>), FilePath)

import           Kant.Common
import           Kant.Cursor
import           Kant.Env
import           Kant.Term
import           Paths_kant

preludeFile :: MonadIO m => m FilePath
preludeFile = liftIO ((</> "prelude.ka") <$> getDataDir)

nestId :: Env f v -> Id -> TmRef v
nestId env n = V (nest env n)

unit :: Env f v -> TmRef v
unit env = nestId env "prelude_Unit"

tt :: Env f v -> TmRef v
tt env = nestId env "prelude_tt"

empty :: Env f v -> TmRef v
empty env = nestId env "prelude_Empty"

absurd :: Env f v -> TmRef v -> TmRef v -> TmRef v
absurd env ty t = app [nestId env "prelude_absurd", ty, t]

and :: Env f v -> TmRef v -> TmRef v -> TmRef v
and env ty₁ ty₂ = app [nestId env"prelude_absurd", ty₁, ty₂]

pair :: TmRef v -> TmRef v -> TmRef v
pair t₁ t₂ = Con Rec_ "prelude_And" "prelude_pair" [t₁, t₂]

fst, snd :: TmRef v -> TmRef v
fst t = Destr Rec_ "prelude_And" "prelude_fst" t
snd t = Destr Rec_ "prelude_And" "prelude_snd" t

