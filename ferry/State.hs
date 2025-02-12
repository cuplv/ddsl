{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module State where

import qualified ClientComm as CC
import Config

import qualified SuperV as SuperV
import SuperV.Example.LogConsensus hiding (NodeId)
import qualified SuperV.Example.LogConsensus as Core
-- import Lang.Rail.Ext.Accum
-- import Lang.Rail.Ext.KeyTree
-- import Lang.Rail.Ext.List

import Control.Concurrent.STM
import Control.Exception (bracket)
import Control.Monad.DebugLog
import Control.Monad.State
import Data.Foldable (for_)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word (Word32)
import Lens.Micro.Platform
import Network.Ccm
import Network.Ccm.Timer (Timer)
import System.IO (Handle,openFile,IOMode(WriteMode))
import System.Posix (Fd)

-- | Client-specific request sequence number
type Csn = Word32

data ClientState
  = ClientState { _sendQ :: Maybe (TQueue CC.Response)
                , _clientCompleted :: Csn
                }

makeLenses ''ClientState

data MainState
  = MainState
    { _stClients :: Map CC.ClientId ClientState
    , _stConf :: NodeConfig
    , _stAppState :: NodeState
    , _stDeferrals :: Int
    , _stMaxPendingProposals :: Int
    , _stReadyFollowers :: Set NodeId
    , _stEndedNodes :: Set NodeId
    , _stInputQ :: TQueue (CC.ClientId, CC.Input)
    , _stPendingProposals :: Seq (Index, Seq (CC.ClientId, Csn))
    , _stIssuedProposals :: Index
    , _stPriority :: Bool
    , _stPersist :: Maybe Fd
    , _stLeaderTimer :: Maybe Timer
    , _stLeader :: Maybe NodeId
    }

makeLenses ''MainState

isPending (Just _) = True
isPending Nothing = False

newClientState :: ClientState
newClientState = ClientState
  { _sendQ = Nothing
  , _clientCompleted = 0
  }

type ExMsg = (NodeId, Int)

type MainT m = StateT MainState (CcmT m)

newMainState :: TQueue (CC.ClientId, CC.Input) -> Maybe Fd -> NodeConfig -> MainState
newMainState inputQ mhandle conf = MainState
  { _stClients = Map.empty
  , _stConf = conf
  , _stAppState = initAppState (conf^.cCore)
  , _stDeferrals = 0
  , _stMaxPendingProposals = 0
  , _stReadyFollowers = Set.empty
  , _stEndedNodes = Set.empty
  , _stInputQ = inputQ
  , _stPendingProposals = Seq.empty
  , _stIssuedProposals = 0
  , _stPriority = False
  , _stPersist = mhandle
  , _stLeaderTimer = Nothing
  , _stLeader = Just (conf^.cCore.cLeader)
  }

runMainT
  :: MainT (LogIO IO) a
  -> TQueue (CC.ClientId, CC.Input)
  -> NodeConfig
  -> Maybe Fd
  -> LogIO IO a
runMainT m q c mh =
  let
    self = c ^. cNodeId
    net = c ^. cCore . cNetwork
    s = newMainState q mh c
    causal = True
    ccmConf = defaultCcmConfig
      & cccHeartbeatMicros .~
        (fromIntegral (c^.cCore.cHeartbeatTimeoutMs) * 1000)
      & cccRetransMicros .~
        (fromIntegral (c^.cCore.cRetransmissionTimeoutMs) * 1000)
  in
    runCcm ccmConf self net (evalStateT m s)

n2r (NodeId w) = Core.NodeId w

r2n (Core.NodeId w) = NodeId w

initAppState :: CoreConfig -> NodeState
initAppState c =
  let
    leader = n2r (c^.cLeader)
    -- The voter/accepter set does not include the leader
    net = Set.map n2r . Set.delete (c^.cLeader) . Map.keysSet $ c^.cNetwork
    voteQuorum = fromIntegral $ (Set.size net `div` 2) + 1
    acceptQuorum = fromIntegral $ (Set.size net `div` 2) + 1
    votes =
      Map.fromList
      . map (\i -> ((Branch 0, i), leader))
      . Set.toList
      $ net
  in
    ( (net, NCount voteQuorum, NCount acceptQuorum)
    , votes
    , (Branch 0, fst SuperV.emptyKt', snd SuperV.emptyKt')
    , SuperV.Accum Map.empty
    )
