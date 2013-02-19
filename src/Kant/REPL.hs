-- TODO write usage
module Kant.REPL (main) where

import           Control.Applicative ((*>), (<$>), (<|>), (<$))
import           Control.Arrow (left)
import           Control.Monad (msum)
import           Control.Exception (catch)
import           Data.Char (isSpace)
import           Prelude hiding (catch)

import           Control.Monad.Error (ErrorT(..))
import           Control.Monad.IO.Class (liftIO)
import qualified Text.Parsec as Parsec
import           Text.Parsec.Char (anyChar, char)

import           System.Console.Haskeline
                 (InputT, getInputLine, runInputT, defaultSettings)
import           System.Console.Haskeline.MonadException ()

import           Kant.Parser
import           Kant.Environment
import           Kant.Reduce
import           Kant.TyCheck
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

parseInput :: String -> Either REPLError Input
parseInput =
    either (Left . CmdParse) Right . Parsec.parse (Parsec.spaces *> go) ""
  where
    go       =     Parsec.string ":" *> msum [char ch *> p | (ch, p) <- commands]
               <|> ISkip <$ Parsec.eof
               <|> IDecl <$> Parsec.many anyChar
    rest     = Parsec.many anyChar
    commands = [ ('e', IEval <$> rest)
               , ('t', ITyCheck <$> rest)
               , ('p', IPretty <$> rest)
               , ('l', ILoad . trim <$> rest)
               , ('q', IQuit <$ Parsec.eof)
               ]

replOutput :: Env -> String -> ErrorT REPLError IO (Output, Env)
replOutput env s₁ =
    do c <- ret (parseInput s₁)
       case c of
           ITyCheck s₂ -> do t <- parse s₂
                             ty <- tyct t
                             return (OTyCheck ty, env)
           IEval s₂    -> do t <- parse s₂
                             tyct t
                             return (OPretty (nf env t), env)
           IDecl s₂    -> do d <- parseE (parseDecl s₂)
                             env' <- tyE (tyCheck env d)
                             return (OOK, env')
           ILoad fp    -> do s <- readSafe fp
                             m <- parseE (parseModule s)
                             env' <- tyE (tyCheck env m)
                             return (OOK, env')
           IPretty s₂  -> do t <- parse s₂
                             return (OPretty (whnf env t), env)
           IQuit       -> return (OQuit, env)
           ISkip       -> return (OSkip, env)
  where
    ret     = ErrorT . return
    parseE  = ret . left TermParse
    tyE     = ret . left TyCheck
    parse   = parseE . parseTerm
    tyct    = tyE . tyCheckT env
    readSafe fp = ErrorT (catch (Right <$> readFile fp) (return . Left . IOError))

repl :: Env -> String -> REPL (Maybe Env)
repl env input =
    do res <- liftIO (runErrorT (replOutput env input))
       case res of
           Left err          -> do liftIO (putPretty err); return (Just env)
           Right (out, env') -> do liftIO (putPretty out); quit out env'
  where quit OQuit _ = return Nothing
        quit _     e = return (Just e)

run :: Env -> REPL ()
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
