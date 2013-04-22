-- TODO write usage
module Kant.REPL (main) where

import           Control.Applicative ((<|>))
import           Control.Exception (catch)
import           Control.Monad (msum, when)
import           Prelude hiding (catch)

import           Control.Monad.IO.Class (liftIO)
import qualified Text.Parsec as Parsec
import           Text.Parsec.Char (anyChar, char)

import           System.Console.Haskeline
                 (InputT, getInputLine, runInputT, defaultSettings)
import           System.Console.Haskeline.MonadException ()

import           Kant.Common
import           Kant.Term
import           Kant.Env
import           Kant.TyCheck
import           Kant.Ref
import           Kant.Elaborate
import           Kant.Pretty
import           Kant.REPL.Types
import           Kant.Monad

type REPL = InputT IO

data Input
    = ITyCheck String
    | IEval String
    | IDecl String
    | ILoad Bool FilePath
    | IPretty String
    | IQuit
    | ISkip

type REPLM = KMonad Id IO

parseInput :: String -> REPLM Input
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

replOutput :: String -> REPLM Output
replOutput s₁ =
    do c <- parseInput s₁
       case c of
           -- Note that here we often discard the generated environments since
           -- all they have changed is the Ref
           ITyCheck s₂ -> do t <- putRef =<< parseTermM s₂
                             (ty, holes) <- tyInfer t
                             ty' <- nfM ty
                             return (OTyCheck ty' holes)
           IEval s₂    -> do t <- putRef =<< parseTermM s₂
                             tyInfer t
                             OPretty <$> nfM t
           IDecl s₂    -> OHoles <$> (elaborate =<< putRef =<< parseDeclM s₂)
           ILoad r fp  -> do s₂ <- readSafe fp
                             m <- putRef =<< parseModuleM s₂
                             when r (putEnv newEnv)
                             OHoles <$> elaborate m
           IPretty s₂  -> OPretty <$> (whnfM =<< putRef =<< parseTermM s₂)
           IQuit       -> return OQuit
           ISkip       -> return OSkip
  where
    readSafe fp =
        do se <- liftIO (catch (Right <$> readFile fp) (return . Left))
           case se of
               Left err -> throwKError (IOError err)
               Right s  -> return s

repl :: EnvId -> String -> REPL (Maybe EnvId)
repl env₁ input =
    do res <- liftIO (runKMonad env₁ (replOutput input))
       case res of
           Left err          -> do liftIO (putPretty err); return (Just env₁)
           Right (out, env₂) -> do liftIO (putPretty out); quit out env₂
  where quit OQuit _ = return Nothing
        quit _     e = return (Just e)

run :: EnvId -> REPL ()
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
