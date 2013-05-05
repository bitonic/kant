-- TODO write usage
module Kant.REPL
    ( Input(..)
    , Output(..)
    , REPL
    , runKMonad
    , replInput
    , replLine
    , repl
    , main
    ) where

import           Control.Applicative ((<|>))
import           Control.Exception (catch)
import           Control.Monad (msum, when, (>=>))

# if __GLASGOW_HASKELL__ < 706
import           Prelude hiding (catch)
# endif

import           Control.Monad.IO.Class (MonadIO(..))
import qualified Text.Parsec as Parsec
import           Text.Parsec.Char (anyChar, char)

import           System.Console.Haskeline
                 (InputT, getInputLine, runInputT, defaultSettings)
import           System.Console.Haskeline.MonadException ()

import           Kant.Common
import           Kant.Elaborate
import           Kant.Env
import           Kant.Monad
import           Kant.Pretty
import           Kant.REPL.Types
import           Kant.Ref
import           Kant.Term
import           Kant.TyCheck

data Input
    = ITyCheck String
    | IEval String
    | IDecl String
    | ILoad Bool FilePath
    | IPretty String
    | IQuit
    | ISkip

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
               ]

replInput :: MonadIO m => Input -> REPL m Output
replInput c =
   case c of
       ITyCheck s -> do t <- putRef =<< parseTmM s
                        (ty, holes) <- tyInfer t
                        ty' <- nfM ty
                        return (OTyCheck ty' holes)
       IEval s    -> do t <- putRef =<< parseTmM s
                        tyInfer t
                        OPretty <$> nfM t
       IDecl s    -> OHoles <$> (elaborate =<< putRef =<< parseDeclM s)
       ILoad r fp -> do when r (putEnv newEnv)
                        s <- readSafe fp
                        m <- putRef =<< parseModuleM s
                        OHoles <$> elaborate m
       IPretty s  -> OPretty <$> (whnfM =<< putRef =<< parseTmM s)
       IQuit      -> return OQuit
       ISkip      -> return OSkip
  where
    readSafe fp =
        do se <- liftIO (catch (Right <$> readFile fp) (return . Left))
           case se of
               Left err -> throwKError (IOError err)
               Right s  -> return s

replLine :: MonadIO m => String -> REPL m Output
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
    do sm <- getInputLine "> "
       case sm of
           Nothing -> run env
           Just s  -> maybe (return ()) run =<< repl env s

banner :: String
banner = "      ___           ___           ___\n" ++
         "     /__/|         /  /\\         /__/\\          ___\n" ++
         "    |  |:|        /  /::\\        \\  \\:\\        /  /\\\n" ++
         "    |  |:|       /  /:/\\:\\        \\  \\:\\      /  /:/\n" ++
         "  __|  |:|      /  /:/~/::\\   _____\\__\\:\\    /  /:/\n" ++
         " /__/\\_|:|____ /__/:/ /:/\\:\\ /__/::::::::\\  /  /::\\\n" ++
         " \\  \\:\\/:::::/ \\  \\:\\/:/__\\/ \\  \\:\\~~\\~~\\/ /__/:/\\:\\\n" ++
         "  \\  \\::/~~~~   \\  \\::/       \\  \\:\\  ~~~  \\__\\/  \\:\\\n" ++
         "   \\  \\:\\        \\  \\:\\        \\  \\:\\           \\  \\:\\\n" ++
         "    \\  \\:\\        \\  \\:\\        \\  \\:\\           \\__\\/\n" ++
         "     \\__\\/         \\__\\/         \\__\\/"

main :: IO ()
main = do putStrLn banner; runInputT defaultSettings (run newEnv)
