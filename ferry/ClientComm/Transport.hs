{-# LANGUAGE FlexibleContexts #-}

module ClientComm.Transport
  ( recvDecoded
  ) where

import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Data.ByteString.Lazy as LBS
import qualified Network.Framed as Framed
import qualified Network.Simple.TCP as TCP

recvDecoded
  :: (MonadError Framed.Exception m, MonadIO m)
  => TCP.Socket
  -> (LBS.ByteString -> Either String a)
  -> String
  -> m a
recvDecoded sock decode decoderName = do
  bytes <- Framed.recv sock
  case decode bytes of
    Right a -> return a
    Left err -> throwError . Framed.ContentException $
      "Could not decode " ++ decoderName ++ ": " ++ err
