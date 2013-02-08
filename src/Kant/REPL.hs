-- TODO write usage
module Kant.REPL (main) where

import           Control.Applicative ((*>), (<$>), (<*), (<|>))
import           Control.Arrow (left)
import           Control.Monad (msum)

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
    | IQuit

parseInput :: String -> Either Error Input
parseInput =
    either (Left . CmdParse) Right . Parsec.parse (Parsec.spaces *> go) ""
  where
    go       =     lex_ ":" *>
                   msum (map (\(ch, p) -> char ch *> p) commands)
               <|> IDecl <$> Parsec.many anyChar
    rest     = Parsec.many anyChar
    spaces p = p <* Parsec.spaces
    lex_ s   = spaces (Parsec.string s)
    commands = [ ('e', IEval    <$> rest)
               , ('t', ITyCheck <$> rest)
               , ('q', spaces (return IQuit))
               ]

replOutput :: Env -> String -> Either Error (Output, Env)
replOutput env s₁ =
    do c <- parseInput s₁
       case c of
           ITyCheck s₂ -> do t <- parse s₂
                             ty <- tyct t
                             return (OTyCheck ty, env)
           IEval s₂    -> do t <- parse s₂
                             tyct t
                             return (OEval (nf env t), env)
           IDecl s₂    -> do d <- left TermParse (parseDecl s₂)
                             env' <- left TyCheck (tyCheck env d)
                             return (ODecl, env')
           IQuit       -> return (OQuit, env)
  where
    parse = left TermParse . parseTerm
    tyct  = left TyCheck . tyCheckT env

repl :: Env -> String -> REPL (Maybe Env)
repl env input =
    case replOutput env input of
        Left err          -> do liftIO (putPretty err); return (Just env)
        Right (out, env') -> do liftIO (putPretty out); quit out env'
  where quit OQuit _ = return (Nothing)
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
