{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -fno-warn-orphans #-}

import           Control.Applicative (Applicative, (<$>), (<|>))
import           Data.String (fromString)

import           Control.Monad.Error (strMsg)
import           Control.Monad.Reader (ReaderT, runReaderT, ask)
import           Control.Monad.Trans (lift, MonadIO(..))
import           System.FilePath ((</>), takeFileName)

import           Data.Aeson (ToJSON(..), (.=))
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy.UTF8 as ByteString
import           Network.WebSockets (WebSockets, Hybi00)
import qualified Network.WebSockets as WebSockets
import qualified Network.WebSockets.Snap as WebSockets
import           Snap.Core (Snap)
import qualified Snap.Core as Snap
import qualified Snap.Http.Server as Snap
import qualified Snap.Util.FileServe as Snap

import           Kant.Env
import           Kant.Error
import           Kant.Pretty
import           Kant.REPL hiding (main, repl)
import           Paths_kant

--- Types

newtype DirRead a = DirRead {unDirRead :: ReaderT FilePath IO a}
    deriving (Functor, Applicative, Monad, MonadIO)

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

repl :: EnvId -> String -> DirRead (EnvId, REPLResult)
repl env₁ input =
    do res <- liftIO (runKMonad env₁ (replLine input))
       case res of
           Left err          -> return (env₁, REPLResult (Left err))
           Right (out, env₂) -> return (env₂, REPLResult (quit out))
  where quit OQuit = Left (strMsg "close your browser, fool!")
        quit out   = Right out

dataDir :: MonadIO m => m FilePath
dataDir = liftIO ((</> "web") <$> getDataDir)

session :: WebSockets.Request -> WebSockets Hybi00 ()
session req = do WebSockets.acceptRequest req; (`go` newEnv) =<< dataDir
  where
    go fp env =
        do msg <- WebSockets.receiveData
           (env', res) <- liftIO (runDirRead (repl env (ByteString.toString msg)) fp)
           WebSockets.sendTextData (Aeson.encode res)
           go fp env'

app :: Snap ()
app = Snap.path "repl" (WebSockets.runWebSocketsSnap session) <|>
      (Snap.serveDirectory =<< dataDir)

main :: IO ()
main = Snap.quickHttpServe app
