{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -fno-warn-orphans #-}

import           Control.Applicative (Applicative)
import           Data.String (fromString)

import           Control.Monad.Error (strMsg)
import           Control.Monad.Reader (ReaderT, runReaderT, ask)
import           Control.Monad.Trans (lift, MonadIO(..))
import           System.FilePath ((</>), takeFileName)

import           Data.Aeson (ToJSON(..), (.=))
import qualified Data.Aeson as Aeson
import           Network.WebSockets (WebSockets, Hybi00)
import qualified Network.WebSockets as WebSockets
import qualified Network.WebSockets.Snap as WebSockets
import           Snap.Core (Snap)
import qualified Snap.Core as Snap
import qualified Snap.Http.Server as Snap

import           Kant.Env
import           Kant.Error
import           Kant.Pretty
import           Kant.REPL hiding (main, repl)
import           Paths_kant

--- Types

newtype DirRead a = DirRead {unDirRead :: ReaderT FilePath IO a}
    deriving (Functor, Applicative, Monad)

runDirRead :: DirRead a -> FilePath -> IO a
runDirRead = runReaderT . unDirRead

instance ReadFile DirRead where
    readFile' fp =
        do dir <- DirRead ask
           if takeFileName dir == dir
              then DirRead (lift (readFile' (dir </> "samples-good" </> fp)))
              else return (Left (strMsg "invalid path"))

newtype REPLResult = REPLResult (Either KError Output)

instance ToJSON KError where
    toJSON = fromString . show . pretty

instance ToJSON Output where
    toJSON = fromString . show . pretty

instance ToJSON REPLResult where
    toJSON (REPLResult res) =
        Aeson.object
            [ "response" .= (either (const "error") (const "ok") res :: String)
            , "body"     .= either toJSON toJSON res ]

repl :: EnvId -> String -> WebSockets p (EnvId, REPLResult)
repl ref s = undefined

session :: WebSockets.Request -> WebSockets Hybi00 ()
session req = undefined

dataFile :: MonadIO m => FilePath -> m FilePath
dataFile fp = liftIO (getDataFileName ("web" </> fp))

app :: Snap ()
app = Snap.route [ ("/",     Snap.sendFile =<< dataFile "index.html")
                 , ("/repl", WebSockets.runWebSocketsSnap session)
                 ]

main :: IO ()
main = Snap.quickHttpServe app
