{-# LANGUAGE DeriveGeneric #-}

module Config.New
  ( NewConfig
  , makeOldConfig
  , getDebugSelector
  , fromString
  ) where

import Network.Ccm (nodeId, NodeId, MyAddr (..))
import Network.Ccm.Extra (SendTarget (..))

import Config (CoreConfig (..), NodeConfig (..))

import Data.Aeson
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TL
import Data.Word (Word32)
import GHC.Generics

data NetMember
  = NetMember
    { memberIndex :: Word32
    , host :: String
    , port :: String
    }
  deriving (Show,Eq,Ord,Generic)

instance ToJSON NetMember where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON NetMember

data NewConfig
  = NewConfig
    { network :: [NetMember]
    , localId :: Word32
    , clientHost :: String
    , clientPort :: String
    , debugSelector :: [String]
    , persistFile :: String
    , electionTimeoutMsLow :: Word32
    , electionTimeoutMsHigh :: Word32
    , retransmissionTimeoutMs :: Word32
    , heartbeatTimeoutMs :: Word32
    }
  deriving (Show,Eq,Ord,Generic)

instance ToJSON NewConfig where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON NewConfig

makeNetwork :: [NetMember] -> Map NodeId MyAddr
makeNetwork =
  foldr
    (\nm a -> Map.insert
      (nodeId $ memberIndex nm)
      (MyAddr (host nm) (port nm))
      a)
    Map.empty

makeOldConfig :: NewConfig -> NodeConfig
makeOldConfig nc = NodeConfig
  { _cNodeId = nodeId (localId nc)
  , _cClientHost = clientHost nc
  , _cClientPort = clientPort nc
  , _cPersist = if persistFile nc == "" then Nothing else Just (persistFile nc)
  , _cCore = CoreConfig
    { _cNetwork = net
    , _cLeader = minimum (Map.keys net)
    -- Used to use 5 sec, but now that the node is managed, we don't
    -- need this.
    , _cRecvTimeout = Nothing
    , _cFollowerChunkMicros = Nothing
    , _cLeaderAcceptBatch = Nothing
    -- Why is this configuration value provided?
    , _cRttMillis = 0
    , _cRequestPollMicros = 0
    , _cElectionTimeoutMsLow = electionTimeoutMsLow nc
    , _cElectionTimeoutMsHigh = electionTimeoutMsHigh nc
    , _cRetransmissionTimeoutMs = retransmissionTimeoutMs nc
    , _cHeartbeatTimeoutMs = heartbeatTimeoutMs nc
    }
  }
  where net = makeNetwork $ network nc

getDebugSelector :: NewConfig -> [String]
getDebugSelector = debugSelector

fromString :: String -> NewConfig
fromString s =
  let
    m = eitherDecode . TL.encodeUtf8 . TL.pack $ s
  in case m of
    Right c -> c
    Left e -> error $ "Config parse failed: " ++ (show e)
