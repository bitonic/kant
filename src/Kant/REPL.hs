-- TODO write usage
{-# LANGUAGE OverloadedStrings #-}
module Kant.REPL
    ( Input(..)
    , Output(..)
    , ReadFile(..)
    , REPL
    , runKMonad
    , replInput
    , replLine
    , repl
    , banner
    , main
    ) where

import           Control.Applicative ((<|>))
import           Control.Exception (catch)
import           Control.Monad (msum, when, (>=>))
import           Data.Version (showVersion)

# if __GLASGOW_HASKELL__ < 706
import           Prelude hiding (catch)
# endif

import           Control.Monad.Trans (lift, MonadIO(..))
import qualified Text.Parsec as Parsec
import           Text.Parsec.Char (anyChar, char)

import           System.Console.Haskeline
                 (InputT, getInputLine, runInputT, defaultSettings)
import           System.Console.Haskeline.MonadException ()

import           Kant.Common
import           Kant.Decl
import           Kant.Elaborate
import           Kant.Env
import           Kant.Error
import           Kant.Monad
import           Kant.Prelude
import           Kant.Pretty
import           Kant.REPL.Types
import           Kant.Term
import           Kant.TyCheck
import           Paths_kant

data Input
    = ITyCheck String
    | IEval String
    | IDecl String
    | ILoad Bool FilePath
    | IPretty String
    | IQuit
    | ISkip
    | IHelp

class Monad m => ReadFile m where
    readFile' :: FilePath -> m (Either IOError String)

instance ReadFile IO where
    readFile' fp = catch (Right <$> readFile fp) (return . Left)

type REPL m = KMonadT Id m

parseInput :: Monad m => String -> REPL m Input
parseInput =
    either (throwKError . CmdParse) return . Parsec.parse (Parsec.spaces *> go) ""
  where
    go       =     Parsec.string ":" *> msum [char ch *> p | (ch, p) <- commands]
               <|> ISkip <$ Parsec.eof
               <|> IDecl <$> rest
    rest     = Parsec.many anyChar
    commands = [ ('e', IEval <$> rest)
               , ('t', ITyCheck <$> rest)
               , ('p', IPretty <$> rest)
               , ('l', ILoad False . trim <$> rest)
               , ('r', ILoad True . trim <$> rest)
               , ('q', IQuit <$ Parsec.eof)
               , ('h', IHelp <$ Parsec.eof)
               ]

replInput :: ReadFile m => Input -> REPL m Output
replInput c =
    -- When we typecheck we restore the old environment, so that stuff like
    -- constraints and references don't uselessly pile up
    case c of
        ITyCheck s -> do t <- processTmM s
                         (ty, holes) <- restoreEnv (tyInfer t)
                         ty' <- nfM ty
                         return (OTyCheck ty' holes)
        IEval s    -> do t <- processTmM s
                         restoreEnv (tyInfer t)
                         OPretty <$> nfM t
        IDecl s    -> OHoles <$> (processDeclM s >>= elaborate)
        ILoad r fp -> do when r (putEnv newEnv)
                         let elab = mapM (conDestrDeclM >=> elaborate) . unModule
                         OHoles . concat <$> (readSafe fp >>= parseModuleM >>= elab)
        IPretty s  -> OPretty <$> (whnfM =<< processTmM s)
        IQuit      -> return OQuit
        ISkip      -> return OSkip
        IHelp      -> return OHelp
  where
    readSafe fp =
        do se <- lift (readFile' fp)
           case se of
               Left err -> throwKError (IOError err)
               Right s  -> return s

replLine :: ReadFile m => String -> REPL m Output
replLine = parseInput >=> replInput

repl :: MonadIO m => EnvId -> String -> m (Maybe EnvId)
repl env₁ input =
    do res <- liftIO (runKMonad env₁ (replLine input))
       case res of
           Left err          -> do liftIO (putPretty err); return (Just env₁)
           Right (out, env₂) -> do liftIO (putPretty out); quit out env₂
  where quit OQuit _ = return Nothing
        quit _     e = return (Just e)

run :: EnvId -> InputT IO ()
run env =
    do sm <- getInputLine ">>> "
       case sm of
           Nothing -> run env
           Just s  -> maybe (return ()) run =<< repl env s

banner :: String
banner = "B E R T U S\nVersion " ++ showVersion version ++
         ", made in London, year 2013."

preludeEnv :: MonadIO m => m EnvId
preludeEnv =
    liftIO $
    do res <- runKMonad newEnv . replInput . ILoad False =<< preludeFile
       case res of
           Left err -> fail ("Error while loading prelude:\n" ++ show (pretty err))
           Right (_, env) -> return env

main :: IO ()
main =
    do putStrLn banner
       runInputT defaultSettings (run =<< preludeEnv)
