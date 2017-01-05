module Session.WebSockets where

import Session

import Control.Exception.Safe (throw, try)
import Control.Monad.IO.Class
import Data.ByteString (ByteString)
import Data.Serialize (Serialize, decode, encode)
import Network.WebSockets (Connection)
import System.Timeout (timeout)

import qualified Network.WebSockets as WebSockets

runWebSocketsSession
  :: MonadIO m
  => Connection -> Session '[] e' r 'Done Serialize m a -> m a
runWebSocketsSession conn s = do
  x <- go s
  liftIO (teardown conn)
  pure x
 where
  go :: MonadIO m => Session e e' r r' Serialize m a -> m a
  go = \case
    SSend x -> sendBytes conn x
    SRecv   -> recvBytes conn
    SEnter  -> pure ()
    SZero   -> pure ()
    SSucc   -> pure ()
    SPickL  -> sendBytes conn True
    SPickR  -> sendBytes conn False

    SOffer s1 s2 ->
      recvBytes conn >>= \case
        True  -> go s1
        False -> go s2

    SPure x -> pure x

    SLift m -> m

    SBind m k -> do
      x <- go m
      go (k x)

sendBytes :: (Serialize a, MonadIO m) => Connection -> a -> m ()
sendBytes conn x = liftIO (WebSockets.sendBinaryData conn (encode x))

recvBytes :: (Serialize a, MonadIO m) => Connection -> m a
recvBytes conn = do
  bytes <- liftIO (WebSockets.receiveData conn)
  case decode bytes of
    Left err -> error err
    Right x  -> pure x

-- Send close frame, receive in-flight messages until client sends close, but
-- don't wait for more than 3 seconds.
teardown :: Connection -> IO ()
teardown conn = do
  WebSockets.sendClose conn ("" :: ByteString)

  let loop :: IO ()
      loop =
        try (WebSockets.receiveDataMessage conn) >>= \case
          Left (WebSockets.CloseRequest _ _) -> pure ()
          Left ex -> throw ex
          Right _ -> loop

  _ <- timeout (3*1000*1000) loop
  pure ()
