#!/usr/bin/env runghc

module Main where

import Control.Concurrent
import System.Environment
import System.Process

main :: IO ()
main = do
    args <- getArgs
    case args of
        (filepath : commands) -> do
            let command = concat commands
            supervisor filepath command "" Nothing
        _ -> do
            putStrLn "Usage: monitor.hs ./plugins/extraction/erlang.ml make"

supervisor :: FilePath -> String -> String -> Maybe ThreadId -> IO ()
supervisor filepath command lastContent workerId = do
    content <- readFile filepath
    if content == lastContent
        then do
            threadDelay 5000000 -- 5 seconds
            supervisor filepath command content workerId
        else do
            maybe (return ()) killThread workerId
            newId <- forkIO (worker command)
            threadDelay 5000000
            supervisor filepath command content (Just newId)

worker :: String -> IO ()
worker command = callCommand command
