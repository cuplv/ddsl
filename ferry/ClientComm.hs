{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module ClientComm
  ( runServer
  , ClientId
  , Input (..)
  , ServerCtx
  , inputQ
  , newCtx
  , Request (..)
  , Response (..)
  , writeQ
  , readQ
  ) where

import ClientComm.Protocol
import ClientComm.Transport

import Control.Concurrent (forkIO,killThread)
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.DebugLog
import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Data.Serialize.Get as Cereal
-- import Data.Time.Clock
-- import Data.Time.Format
import Lens.Micro.Platform
import qualified Network.Framed as Framed
import qualified Network.Simple.TCP as TCP

data Input
  = Request Request
  | Connect (TQueue Response)
  | Disconnect

instance Show Input where
  show i = case i of
    Request r -> "Request(" ++ show r ++ ")"
    Connect _ -> "Connect(...)"
    Disconnect -> "Disconnect"

data ServerCtx
  = ServerCtx { _inputQ :: TQueue (ClientId, Input)
              }

makeLenses ''ServerCtx

newCtx :: (MonadIO m) => m ServerCtx
newCtx = do
  inputQ <- liftIO newTQueueIO
  return $ ServerCtx
    { _inputQ = inputQ
    }

-- | Listen on an interface, forking 'runProtocol' threads for each
-- new connection.
runServer
  :: TCP.HostPreference
  -> TCP.ServiceName
  -> ServerCtx
  -> LogIO IO ()
runServer host port ctx = do
  f <- passLogIOF $ \(sock,_) -> runProtocol ctx sock
  dlog ["connection"] $
    "Running ClientComm server on "
    ++ show host
    ++ ", "
    ++ show port
  liftIO $ TCP.serve host port f

writeQ :: (MonadIO m) => TQueue a -> a -> m ()
writeQ q a = liftIO . atomically $ writeTQueue q a

readQ :: (MonadIO m) => TQueue a -> m a
readQ q = liftIO . atomically $ readTQueue q

-- | Receive the message from the client, which specifies its
-- 'ClientId', and then exchange messages with the client until the
-- socket connection dies.
runProtocol
  :: ServerCtx
  -> TCP.Socket
  -> LogIO IO ()
runProtocol ctx sock = do
  clientId <- runExceptT $ Framed.recvWord16 sock
  case clientId of
    Left e ->
      dlog ["error"] $ "Server failed to accept client: " ++ show e
    Right clientId -> do
      dlog ["trace"] $ "Server connected to C" ++ show clientId

      -- Create queue for sending messages to client.
      outputQ <- liftIO newTQueueIO
      -- Fork a thread to send messages to client.
      sendAction <- passLogIO $ sendThread sock outputQ clientId
      sendId <- liftIO . forkIO $ sendAction
      -- Pass send-queue to central thread.
      writeQ (ctx^.inputQ) (clientId, Connect outputQ)

      -- Receive client messages until connection ends.
      err <- runExceptTF $ recvStep ctx sock clientId
      dlog ["error"] $
        "Server recv-loop for C"
        ++ show clientId
        ++ " ended with "
        ++ show err
      writeQ (ctx^.inputQ) (clientId, Disconnect)
      -- Kill send-loop thread (since it won't die on its own until it
      -- fails to send a message).
      liftIO $ killThread sendId

-- | Repeatedly send encoded 'Response's from a 'TQueue' to the
-- socket.  The 'ClientId' is provided solely for a log message.
sendThread
  :: (MonadIO m, MonadLog m)
  => TCP.Socket
  -> TQueue Response
  -> ClientId
  -> m ()
sendThread sock q clientId = do
  err <- runExceptTF $ do
    response <- readQ q
    Framed.send sock (encodeResponse response)
  dlog ["error"] $
    "Server send-loop for C"
    ++ show clientId
    ++ " failed with "
    ++ show err

-- | Receive a 'Request' from the client and pass it via
-- 'TQueue' to the central thread.
recvStep
  :: (MonadIO m, MonadError Framed.Exception m, MonadLog m)
  => ServerCtx
  -> TCP.Socket
  -> ClientId
  -> m ()
recvStep ctx sock clientId = do
  request <- recvRequest sock
  dlog ["trace"] $
    "Server got request "
    ++ show request
    ++ " from C"
    ++ show clientId
  writeQ (ctx^.inputQ) (clientId, Request request)

-- | Receive a message and decode it to a 'Request'.
recvRequest
  :: (MonadIO m, MonadError Framed.Exception m)
  => TCP.Socket
  -> m Request
recvRequest sock = recvDecoded sock decodeRequest "Request"

-- | Run an 'ExceptT' action repeatedly until it throws an exception,
-- and then return the exception.
runExceptTF :: (Monad m) => ExceptT e m a -> m e
runExceptTF m = do
  result <- runExceptT . forever $ m
  case result of
    Left e -> return e
    Right _ -> error "runExceptTF ended without exception?"
