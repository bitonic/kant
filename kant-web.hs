-- TODO More sensible timeouts
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Takes a 'Kant.REPL' and puts it behind a WebSockets server.
import           Control.Applicative (Applicative, (<$>), (<|>))
import           Data.String (fromString)

import           Control.Monad.Error (strMsg)
import           Control.Monad.Reader (ReaderT, runReaderT, ask)
import           Control.Monad.Trans (lift, MonadIO(..))
import           System.FilePath ((</>), splitFileName)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as TextLazy

import           Data.Aeson (ToJSON(..), (.=))
import qualified Data.Aeson as Aeson
import           Network.WebSockets (WebSockets, Hybi10)
import qualified Network.WebSockets as WebSockets
import qualified Network.WebSockets.Snap as WebSockets
import           Snap.Core (Snap)
import qualified Snap.Core as Snap
import qualified Snap.Http.Server as Snap
import qualified Snap.Util.FileServe as Snap
import           Text.Pandoc

import           Kant.Env
import           Kant.Error
import           Kant.Pretty
import           Kant.REPL hiding (main, repl)
import           Paths_kant

-- | 'ReadFile' that will allow only files in 'data/samples/good' to be read.
newtype DirRead a = DirRead {unDirRead :: ReaderT FilePath IO a}
    deriving (Functor, Applicative, Monad, MonadIO)

runDirRead :: DirRead a -> FilePath -> IO a
runDirRead = runReaderT . unDirRead

instance ReadFile DirRead where
    readFile' fp =
        do dir <- DirRead ask
           if snd (splitFileName fp) == fp
              then DirRead (lift (readFile' (dir </> fp)))
              else return (Left (strMsg ("Invalid filename `" ++ fp ++ "'")))

-- | What we give back to the client, will be rendered in JSON glory as
--   @{status: "ok" + "error", body: String}@
newtype Message a = Message (Either KError a)

instance ToJSON KError where
    toJSON = fromString . show . pretty

instance ToJSON Output where
    toJSON = fromString . show . pretty

instance ToJSON a => ToJSON (Message a) where
    toJSON (Message res) =
        Aeson.object
            [ "status" .= (either (const "error") (const "ok") res :: String)
            , "body"   .= either toJSON toJSON res ]

repl :: EnvId -> String -> DirRead (EnvId, Message Output)
repl env₁ input =
    do res <- runKMonad env₁ (replLine input)
       case res of
           Left err          -> return (env₁, Message (Left err))
           Right (out, env₂) -> return (env₂, Message (quit out))
  where quit OQuit = Left (strMsg "Close your browser, fool!")
        quit out   = Right out

session :: WebSockets.Request -> WebSockets Hybi10 ()
session req =
    do WebSockets.acceptRequest req
       WebSockets.spawnPingThread 5
       WebSockets.sendTextData (Aeson.encode (Message (Right banner)))
       (`go` newEnv) =<< ((</> "samples/good") <$> liftIO getDataDir)
  where
    go fp env =
        do msg <- WebSockets.receiveData
           (env', res) <- liftIO (runDirRead (repl env (Text.unpack msg)) fp)
           WebSockets.sendTextData (Aeson.encode res)
           go fp env'

app :: TextLazy.Text -> Snap ()
app ix =
    Snap.path "repl" (Snap.modifyTimeout (const 10) >>
                      WebSockets.runWebSocketsSnap session)
    <|> Snap.path "" (Snap.writeLazyText ix) -- Index
    <|> (Snap.serveDirectory =<< publicDir)

publicDir :: MonadIO m => m FilePath
publicDir = liftIO ((</> "web/public") <$> getDataDir)

-- | Pulls the index page template in, injects the markdown overview via Pandoc,
--   returns the result.
index :: IO String
index =
    do dir <- getDataDir
       tmpl <- readFile (dir </> "web/index-template.html")
       md <- readMarkdown def{readerSmart = True} <$>
             readFile (dir </> "docs/overview.md")
       return (writeHtmlString def{writerStandalone = True, writerTemplate = tmpl} md)

main :: IO ()
main = Snap.quickHttpServe . app . TextLazy.pack =<< index
