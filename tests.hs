{-# LANGUAGE OverloadedStrings #-}
import           Control.Applicative ((<$>))
import           Data.List ((\\))

import           System.Directory (getDirectoryContents)
import           System.FilePath ((</>))

import           Test.Framework (defaultMain)
import           Test.Framework.Providers.HUnit (hUnitTestToTests)
import           Test.HUnit
import           Text.PrettyPrint.Leijen ((<$$>), nest)

import           Kant.Env
import           Kant.Error
import           Kant.Monad
import           Kant.Pretty
import           Kant.REPL hiding (main)
import           Paths_kant

dataFiles :: FilePath -> IO [FilePath]
dataFiles fp =
    do full <- (</> fp) <$> getDataDir
       (map (full </>) . (\\ [".", ".."])) <$> getDirectoryContents full

loadFile :: FilePath -> IO (Either KError Output)
loadFile fp =
    do res <- runKMonad newEnv (replInput (ILoad False fp))
       return $ case res of
                    Left err       -> Left err
                    Right (out, _) -> Right out

assertGood :: Either KError Output -> IO ()
assertGood (Left err) =
    assertFailure (show (nest 2 ("Expecting the REPL to succeed, got" <$$> pretty err)))
assertGood (Right _) = return ()

assertBad :: Either KError Output -> IO ()
assertBad (Left _)  = return ()
assertBad (Right _) = assertFailure "Expecting the REPL to succeed"

goodSamples :: IO Test
goodSamples =
    do goodies <- dataFiles "samples/good"
       let ts = [test (loadFile fp >>= assertGood) | fp <- goodies]
       return (TestLabel "Good samples" (TestList ts))

badSamples :: IO Test
badSamples =
    do baddies <- dataFiles "samples/bad"
       let ts = [test (loadFile fp >>= assertBad) | fp <- baddies]
       return (TestLabel "Bad samples" (TestList ts))

tests :: IO Test
tests = TestList <$> sequence [goodSamples, badSamples]

main :: IO ()
main = defaultMain . hUnitTestToTests =<< tests
