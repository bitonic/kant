-- TODO write usage
module Kant.REPL (main) where

import           Control.Applicative ((*>), (<$>), (<|>), (<$))
import           Control.Arrow (left)
import           Control.Exception (catch)
import           Control.Monad (msum)
import           Data.Char (isSpace)
import           Prelude hiding (catch)

import           Control.Monad.Error (ErrorT(..), throwError, mapErrorT)
import           Control.Monad.IO.Class (liftIO)
import qualified Text.Parsec as Parsec
import           Text.Parsec.Char (anyChar, char)

import           System.Console.Haskeline
                 (InputT, getInputLine, runInputT, defaultSettings)
import           System.Console.Haskeline.MonadException ()

import           Kant.Parser
import           Kant.Env
import           Kant.Reduce
import           Kant.TyCheck
import           Kant.Elaborate
import           Kant.Pretty
import           Kant.REPL.Types

type REPL = InputT IO

data Input
    = ITyCheck String
    | IEval String
    | IDecl String
    | ILoad FilePath
    | IPretty String
    | IQuit
    | ISkip

trim :: String -> String
trim = reverse . f . reverse . f where f = dropWhile isSpace

type REPLM = ErrorT REPLError IO

parseInput :: String -> REPLM Input
parseInput =
    either (throwError . CmdParse) return . Parsec.parse (Parsec.spaces *> go) ""
  where
    go       =     Parsec.string ":" *> msum [char ch *> p | (ch, p) <- commands]
               <|> ISkip <$ Parsec.eof
               <|> IDecl <$> rest
    rest     = Parsec.many anyChar
    commands = [ ('e', IEval <$> rest)
               , ('t', ITyCheck <$> rest)
               , ('p', IPretty <$> rest)
               , ('l', ILoad . trim <$> rest)
               , ('q', IQuit <$ Parsec.eof)
               ]

mapTyCheckM :: ErrorT TyCheckError IO a -> REPLM a
mapTyCheckM = mapErrorT (left TyCheck <$>)

replOutput :: EnvId -> String -> REPLM (Output, EnvId)
replOutput env₁ s₁ =
    do c <- parseInput s₁
       case c of
           ITyCheck s₂ -> do t <- parse s₂
                             ty <- tyct env₁ t
                             return (OTyCheck (nf env₁ ty), env₁)
           IEval s₂    -> do t <- parse s₂
                             tyct env₁ t
                             let t' = nf env₁ t
                             return (OPretty t', env₁)
           IDecl s₂    -> do d <- parseE (parseDecl s₂)
                             env₂ <- elab env₁ d
                             return (OOK, env₂)
           ILoad fp    -> do s₂ <- readSafe fp
                             m <- parseE (parseDecl s₂)
                             env₂ <- elab env₁ m
                             return (OOK, env₂)
           IPretty s₂  -> do t <- whnf env₁ <$> parse s₂
                             return (OPretty t, env₁)
           IQuit       -> return (OQuit, env₁)
           ISkip       -> return (OSkip, env₁)
  where
    parseE (Left pe) = throwError (TermParse pe)
    parseE (Right x) = return x
    parse = parseE . parseTerm
    tyct env = mapTyCheckM . tyCheck env
    elab env = mapTyCheckM . elaborate env
    readSafe fp =
        do se <- liftIO (catch (Right <$> readFile fp) (return . Left))
           case se of
               Left err -> throwError (IOError err)
               Right s  -> return s

repl :: EnvId -> String -> REPL (Maybe EnvId)
repl env₁ input =
    do res <- liftIO (runErrorT (replOutput env₁ input))
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
