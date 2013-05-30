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
import           Kant.Monad.Base
import           Kant.Term
import           Paths_kant

preludeFile :: MonadIO m => m FilePath
preludeFile = liftIO ((</> "prelude.ka") <$> getDataDir)

nestId :: Monad m => Id -> KMonadE f v m (TmRef v)
nestId n =
    do env <- getEnv
       return (V (nest env n))

unit :: Monad m => KMonadE f v m (TmRef v)
unit = nestId "prelude_Unit"

tt :: Monad m => KMonadE f v m (TmRef v)
tt = nestId "prelude_tt"

empty :: Monad m => KMonadE f v m (TmRef v)
empty = nestId "prelude_Empty"

absurd :: Monad m => TmRef v -> TmRef v -> KMonadE f v m (TmRef v)
absurd ty t =
    do absu <- nestId "prelude_absurd"
       return (app [absu, ty, t])

and :: Monad m => TmRef v -> TmRef v -> KMonadE f v m (TmRef v)
and ty₁ ty₂ =
    do tycon <- nestId "prelude_absurd"
       return (app [tycon, ty₁, ty₂])

pair :: Monad m => TmRef v -> TmRef v -> KMonadE f v m (TmRef v)
pair t₁ t₂ = return (Con Rec_ "prelude_And" "prelude_pair" [t₁, t₂])

fst, snd :: Monad m => TmRef v -> KMonadE f v m (TmRef v)
fst t = return (Destr Rec_ "prelude_And" "prelude_fst" t)
snd t = return (Destr Rec_ "prelude_And" "prelude_snd" t)

