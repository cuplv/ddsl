module ClientComm.Protocol where

import Ddsl.Example.LogConsensus (NodeId (..))

import Control.Concurrent.STM (TQueue)
import qualified Data.ByteString as SBS
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Serialize.Get as Cereal
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8')
import Data.Word (Word8,Word16,Word32)

type ClientId = Word16

data Request
  = RequestEntry Word32 Text
  | Status
  | Die
  deriving (Show,Eq,Ord)

numEntry :: Word8
numEntry = 0

numStatus :: Word8
numStatus = 1

numDie :: Word8
numDie = 2

-- | A request takes one of two forms, distinguished by the "tag"
-- (first byte).
--
-- 0 marks an entry request: a word32Be defining the client-specific
-- sequence number followed by a utf8 text string.
--
-- 1 marks a stataus request, with no content.
--
-- 2 marks a "Die" command, for testing.
decodeRequest :: LBS.ByteString -> Either String Request
decodeRequest bs = do
  let
    getter = do
      tag <- Cereal.getWord8
      case tag of
        t | t == numStatus -> return Status
        t | t == numDie -> return Die
        t | t == numEntry -> do
          sn <- Cereal.getWord32be
          r <- Cereal.remaining
          entryBytes <- Cereal.getBytes r
          case decodeUtf8' entryBytes of
            Right entry -> return $ RequestEntry sn entry
            Left err -> fail (show err)
        t -> fail $ "Unrecognized client request tag " ++ show t
  Cereal.runGetLazy getter bs

{- | Response to send to client. -}
data Response
  = Completed Word32
    -- ^ All entries up to the given client-local sequence number
    -- ('Word32') have been committed.
  | NoLeader
    -- ^ Requests cannot be accepted, temporarily, because this node
    -- does not recognize any leader.  This means that an election is
    -- under way.
  | LeaderIs NodeId
    -- ^ Requests should be sent to the given leader 'NodeId'.
  | Resubmit Word32
    -- ^ Requests following the given client-local sequence number are
    -- not in the new leader's log, and must be re-requested.
  deriving (Show,Eq,Ord)

numCompleted :: Word8
numCompleted = 0

numNoLeader :: Word8
numNoLeader = 1

numLeaderIs :: Word8
numLeaderIs = 2

numResubmit :: Word8
numResubmit = 3

encodeResponse :: Response -> LBS.ByteString
encodeResponse r = case r of
  Completed sn -> Builder.toLazyByteString $
    Builder.word8 numCompleted <> Builder.word32BE sn
  NoLeader -> Builder.toLazyByteString $
    Builder.word8 numNoLeader
  LeaderIs (NodeId nn) -> Builder.toLazyByteString $
    Builder.word8 numLeaderIs <> Builder.word32BE nn
  Resubmit sn -> Builder.toLazyByteString $
    Builder.word8 numResubmit <> Builder.word32BE sn
