{-# LANGUAGE NoMonomorphismRestriction #-}
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
import           Control.Monad.State (StateT(..))
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

type REPLM = ErrorT REPLError (StateT Env IO)

parseInput :: String -> REPLM Input
parseInput =
    either (throwError . CmdParse) return . Parsec.parse (Parsec.spaces *> go) ""
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

mapTyCheckM :: ErrorT TyCheckError (StateT Env IO) a -> REPLM a
mapTyCheckM = mapErrorT (left TyCheck <$>)

replOutput :: String -> REPLM Output
replOutput s₁ =
    do c <- parseInput s₁
       case c of
           ITyCheck s₂ -> do t <- parse s₂
                             ty <- tyct t
                             return (OTyCheck ty)
           IEval s₂    -> do t <- parse s₂
                             tyct t
                             t' <- nf t
                             return (OPretty t')
           IDecl s₂    -> do d <- parseDecl' s₂ >>= parseE
                             tyck d
                             return OOK
           ILoad fp    -> do s <- readSafe fp
                             m <- parseModule' s >>= parseE
                             tyck m
                             return OOK
           IPretty s₂  -> do t <- parse s₂ >>= whnf
                             return (OPretty t)
           IQuit       -> return OQuit
           ISkip       -> return OSkip
  where
    parseE (Left pe) = throwError (TermParse pe)
    parseE (Right x) = return x
    parse s = parseTerm' s >>= parseE
    tyct = mapTyCheckM . tyCheckT
    tyck = mapTyCheckM . tyCheck
    readSafe fp =
        do se <- liftIO (catch (Right <$> readFile fp) (return . Left))
           case se of
               Left err -> throwError (IOError err)
               Right s  -> return s

repl :: Env -> String -> REPL (Maybe Env)
repl env input =
    do (res, env') <- liftIO (runStateT (runErrorT (replOutput input)) env)
       case res of
           Left err  -> do liftIO (putPretty err); return (Just env)
           Right out -> do liftIO (putPretty out); quit out env'
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
