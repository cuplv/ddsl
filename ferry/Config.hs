{-# LANGUAGE TemplateHaskell #-}

module Config where

import Network.Ccm (nodeId, NodeId, MyAddr (..))
import Network.Ccm.Extra (SendTarget (..))

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word (Word32)
import Lens.Micro.Platform

data CoreConfig
  = CoreConfig
    { _cNetwork :: Map NodeId MyAddr
    , _cLeader :: NodeId
    , _cRecvTimeout :: Maybe Int
    , _cFollowerChunkMicros :: Maybe Int
    , _cLeaderAcceptBatch :: Maybe Int
    , _cRttMillis :: Int
    , _cRequestPollMicros :: Int
    , _cElectionTimeoutMsLow :: Word32
    , _cElectionTimeoutMsHigh :: Word32
    , _cRetransmissionTimeoutMs :: Word32
    , _cHeartbeatTimeoutMs :: Word32
    }
    deriving (Show)

makeLenses ''CoreConfig

data NodeConfig
  = NodeConfig
    { _cCore :: CoreConfig
    , _cNodeId :: NodeId
    , _cClientHost :: String
    , _cClientPort :: String
    , _cPersist :: Maybe FilePath
    }
    deriving (Show)

makeLenses ''NodeConfig

getNodeIds :: CoreConfig -> Set NodeId
getNodeIds c = Map.keysSet $ c ^. cNetwork

getFollowers :: CoreConfig -> Set NodeId
getFollowers c =
  Set.delete (c ^. cLeader) (getNodeIds c)

confSelf :: NodeConfig -> NodeId
confSelf c = c ^. cNodeId

getLeaderTarget :: CoreConfig -> SendTarget
getLeaderTarget c = SendTo . Set.singleton $ c ^. cLeader

getFollowersTarget :: CoreConfig -> SendTarget
getFollowersTarget = SendTo . getFollowers
