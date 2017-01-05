module Main where

import PrintSession

import Control.Concurrent.Async
import Network.WebSockets
import Session.WebSockets

main :: IO ()
main = do
  let serverThread = do
        runServer "0.0.0.0" 8008
          (\pconn -> do
            conn <- acceptRequest pconn
            runWebSocketsSession conn server)

      clientThread = do
        runClient "0.0.0.0" 8008 "/"
          (\conn -> do
            runWebSocketsSession conn client)

  race_ serverThread clientThread
