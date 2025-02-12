{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module AppState where

import qualified ClientComm as CC
import Config
import State

import SuperV (Alp,Avs)
import qualified SuperV
import SuperV.Example.LogConsensus hiding (NodeId)
import qualified SuperV.Example.LogConsensus as Core

import Control.Concurrent (forkIO,threadDelay)
import Control.Concurrent.STM
import Control.Monad.DebugLog
import Control.Monad.Except
import Control.Monad.State
import Data.ByteString (ByteString,hPut)
import Data.Foldable (for_,toList,foldl')
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Store as Store
import Data.Store.TH (makeStore)
import Lens.Micro.Platform
import Network.Ccm (NodeId)
import qualified Network.Ccm as Ccm
import qualified Network.Ccm.Extra as Extra
import Network.Ccm.Timer
import System.IO (hFlush)
import qualified System.Posix.ByteString as PBIO
import System.Random

data FerryMsg
  = Vote VoteE
  | Propose ProposeE
  | Accept AcceptE
  deriving (Show,Eq,Ord)

makeStore ''FerryMsg

data ExpMsg
  = Raft (Seq FerryMsg)
  | ReadySignal NodeId
  | EndSignal NodeId
  deriving (Show,Eq,Ord)

makeStore ''ExpMsg

extractFerryMsgs :: ExpMsg -> Seq FerryMsg
extractFerryMsgs m = case m of
  Raft ms -> ms
  ReadySignal _ -> Seq.Empty
  EndSignal _ -> Seq.Empty

encodeExpMsg :: ExpMsg -> ByteString
encodeExpMsg = Store.encode

decodeExpMsg :: ByteString -> Either Store.PeekException ExpMsg
decodeExpMsg = Store.decode

class (Avs a) => FerryMsgV a where
  intoFerryMsg :: a -> FerryMsg

instance FerryMsgV VoteE where
  intoFerryMsg = Vote

instance FerryMsgV ProposeE where
  intoFerryMsg = Propose

instance FerryMsgV AcceptE where
  intoFerryMsg = Accept

handleFerryMsg :: FerryMsg -> NodeState -> NodeState
handleFerryMsg m s = case m of
  Vote v -> SuperV.alpFun (SuperV.from2 handleVote) (v,s)
  Propose p -> SuperV.alpFun (SuperV.from2 handlePropose) (p,s)
  Accept a -> SuperV.alpFun (SuperV.from2 handleAccept) (a,s)

type MsgGen a e = Alp (Core.NodeId,NodeState,a) (Bool,e)

icSelf :: (Monad m) => MainT m Core.NodeId
icSelf = n2r <$> use (stConf . cNodeId)

genFerryMsg :: (Monad m, Avs a, FerryMsgV e) => MsgGen a e -> a -> ExceptT () (MainT m) FerryMsg
genFerryMsg g a = do
  self <- lift $ use $ stConf . cNodeId
  s1 <- lift $ use stAppState
  let
    (ok,mv) = SuperV.alpFun g (n2r self, s1, a)
    rm = intoFerryMsg mv
  if not ok
    then throwError ()
    else do
      lift $ stAppState %= handleFerryMsg rm
      return rm

{-| Attempt to generate and send a message batch, consisting of a
  sequence of generated Raft messages.  An error is thrown if any
  generator fails. -}
sendMsg :: (MonadIO m, MonadLog m, Avs a, FerryMsgV e) => [(MsgGen a e, a)] -> MainT m ()
sendMsg [] = return ()
sendMsg gs = do
  genResult <- runExceptT (traverse (uncurry genFerryMsg) $ Seq.fromList gs)
  case genResult of
    Left () -> error $ "Message generator failed"
    Right rms -> do
      let bytes = encodeExpMsg $ Raft rms
      persist <- use stPersist
      case persist of
        Just h -> liftIO $ do
          PBIO.fdWrite h bytes
          PBIO.fileSynchronise h
        Nothing -> return ()
      lift $ Ccm.publish bytes
      verboseLn $ "Sent msgs: " ++ show rms

{-| Decode a sequence of 'ExpMsg's, returning the set of 'NodeId's for
  which a 'ReadySignal' was received, and the sequence of 'FerryMsg's
  that were received.  If any message could not be decoded, return
  error (and undecodable 'ByteString') instead. -}
decodeManyMsgs
  :: Seq ByteString
  -> Either (Store.PeekException, ByteString) (Set NodeId, Set NodeId, Seq FerryMsg)
decodeManyMsgs rawMsgs = runExcept $ do
  let
    decf :: ByteString -> Except (Store.PeekException, ByteString) ExpMsg
    decf m = case decodeExpMsg m of
      Right em -> return em
      Left e -> throwError (e,m)
    f (ready, ended, raft) em = case em of
      Raft rs -> (ready, ended, raft Seq.>< rs)
      ReadySignal i -> (Set.insert i ready, ended, raft)
      EndSignal i -> (ready, Set.insert i ended, raft)
  msgs <- traverse decf rawMsgs
  return $ foldl' f (Set.empty, Set.empty, Seq.Empty) msgs

{-| Process the output of 'Ccm'.  First, record the number of deferred
  messages.  Second, update the 'stReadyFollowers' set.  Third, apply
  any received 'FerryMsg's to the Raft state. -}
processManyMsgs
  :: (MonadIO m, MonadLog m)
  => Seq (NodeId, ByteString)
  -> ExceptT (Store.PeekException, ByteString) (MainT m) (Seq FerryMsg)
processManyMsgs rawMsgs = do

  case decodeManyMsgs (fmap snd rawMsgs) of
    Left e -> throwError e
    Right (ready,ended,raftMsgs) -> do
      -- Record any newly-ready followers
      lift $ stReadyFollowers %= (Set.union ready)

      -- Record any newly-ended nodes
      lift $ stEndedNodes %= (Set.union ended)

      -- Apply any FerryMsgs
      for_ raftMsgs $ \m -> do
        lift $ stAppState %= handleFerryMsg m

      -- Return any received FerryMsgs
      return raftMsgs

peerOrClient
  :: (MonadIO m, MonadLog m)
  => Bool
  -> MainT m (Either (Seq FerryMsg) [(CC.ClientId, CC.Input)])
peerOrClient priority = do
  clientQ <- use stInputQ
  awaitPeer <- lift Ccm.awaitExchange
  let
    recvClient = do
      b <- isEmptyTQueue clientQ
      if b
        then retry
        else flushTQueue clientQ
  result <- liftIO . atomically $
    if priority
    then (Left <$> awaitPeer) `orElse` (Right <$> recvClient)
    else (Right <$> recvClient) `orElse` (Left <$> awaitPeer)
  case result of
    Right a -> return $ Right a
    Left eCommand -> do
      (liveNodes, ccmsgs) <- lift $ Ccm.exchange eCommand
      processResult <- runExceptT $ processManyMsgs ccmsgs
      case processResult of
        Left e -> error $ "Decode failure in AppState::recvMsgsWithLimit " ++ show e
        Right rms -> return $ Left rms

data PCT
  = GotPeer Ccm.Exchange
  | GotClient [(CC.ClientId, CC.Input)]
  | GotTimer

peerOrClientOrTimer
  :: (MonadIO m, MonadLog m)
  => Bool
  -> MainT m (Maybe (Either (Seq FerryMsg) [(CC.ClientId, CC.Input)]))
peerOrClientOrTimer priority = do
  timer <- use stLeaderTimer
  let
    awaitT = case timer of
      Just t -> awaitTimer t
      Nothing -> retry
  clientQ <- use stInputQ
  awaitPeer <- lift Ccm.awaitExchange
  let
    recvClient = do
      b <- isEmptyTQueue clientQ
      if b
        then retry
        else flushTQueue clientQ
  result <- liftIO . atomically $
    if priority
    then (GotTimer <$ awaitT) `orElse` (GotPeer <$> awaitPeer) `orElse` (GotClient <$> recvClient)
    else (GotTimer <$ awaitT) `orElse` (GotClient <$> recvClient) `orElse` (GotPeer <$> awaitPeer)
  case result of
    GotTimer -> return Nothing
    GotClient a -> return $ Just (Right a)
    GotPeer eCommand -> do
      (liveNodes, ccmsgs) <- lift $ Ccm.exchange eCommand
      processResult <- runExceptT $ processManyMsgs ccmsgs

      -- Restart leader timer if we have a leader and the leader is
      -- among 'liveNodes'.
      refreshLeader liveNodes
      

      case processResult of
        Left e -> error $ "Decode failure in AppState::recvMsgsWithLimit " ++ show e
        Right rms -> return $ Just (Left rms)


{-| Receive messages and apply them to the application state.  Any received 'FerryMsg's are returned. -}
recvMsgs :: (MonadIO m, MonadLog m) => MainT m (Seq FerryMsg)
recvMsgs = do
  await <- lift $ Ccm.awaitExchange
  eCommand <- liftIO . atomically $ await
  (liveNodes,ccmsgs) <- lift $ Ccm.exchange eCommand
  processResult <- runExceptT $ processManyMsgs ccmsgs
  case processResult of
    Left e -> error $ "Decode failure in AppState::recvMsgs " ++ show e
    Right rms -> return rms

queryState :: (Monad m, Avs a, Avs b) => a -> Alp (a,NodeState) b -> MainT m b
queryState a m = do
  s <- use stAppState
  return $ SuperV.alpFun m (a,s)

sendReadySignal :: (MonadIO m, MonadLog m) => MainT m ()
sendReadySignal = do
  self <- use $ stConf . cNodeId
  let msg = encodeExpMsg $ ReadySignal self
  lift $ Ccm.publish msg
  return ()

sendEndSignal :: (MonadIO m, MonadLog m) => MainT m ()
sendEndSignal = do
  self <- use $ stConf . cNodeId
  let msg = encodeExpMsg $ EndSignal self
  lift $ Ccm.publish msg
  return ()

verboseLn :: (MonadLog m) => String -> m ()
verboseLn = dlog ["verbose"]

nextFreshBranch :: (Monad m) => MainT m Branch
nextFreshBranch = do
  (_,vs, (t1,_,_), _) <- use stAppState
  let
    t2 = foldr (\(t',_) t -> max t t') t1 (Map.keys vs)
  return (t2 + 1)

clientBroadcast :: (MonadIO m) => CC.Response -> MainT m ()
clientBroadcast msg = do
  cs <- use stClients
  for_ cs $ \c -> case c^.sendQ of
    Just sq -> do CC.writeQ sq msg
    Nothing -> return ()

refreshLeader :: (MonadIO m, MonadLog m) => Set NodeId -> MainT m ()
refreshLeader s = do
  dlog ["refresh"] $ "Running 'refreshLeader' for " ++ show s
  leader <- use stLeader
  timer <- use stLeaderTimer
  case (leader,timer) of
    (Just l,Just _) | Set.member l s -> do
      dlog ["refresh"] $ "Refreshing leader " ++ show l
      startElectionTimer
    _ -> return ()

getRandomLeaderTimeoutMicros :: (MonadIO m) => MainT m Int
getRandomLeaderTimeoutMicros = do
  low <- use $ stConf.cCore.cElectionTimeoutMsLow
  high <- use $ stConf.cCore.cElectionTimeoutMsHigh
  ms <- randomRIO (low,high)
  -- Convert to Int microseconds
  return (fromIntegral ms * 1000)

startElectionTimer :: (MonadIO m) => MainT m ()
startElectionTimer = do
  -- if timer already exists, cancel it
  t0 <- use stLeaderTimer
  case t0 of
    Just t -> cancelTimer t
    Nothing -> return ()

  -- Set up election timeout
  micros <- getRandomLeaderTimeoutMicros
  t <- forkTimer micros  
  stLeaderTimer .= Just t

checkForLeader :: (MonadIO m, MonadLog m) => MainT m (Maybe Core.NodeId)
checkForLeader = do
  self <- n2r <$> lift Ccm.getSelf
  ns <- ((self:) . fmap n2r . Set.toList) <$> lift Ccm.getPeers
  t <- (\t -> t - 1) <$> nextFreshBranch
  s <- use $ stAppState . _1
  vs <- use $ stAppState . _2
  let
    result = flip List.find ns $ \r ->
      SuperV.alpFun (SuperV.from4 isElected) (t,r,s,vs)
  case result of
    Just r -> do
      dlog ["election"] $ "Leader is " ++ show r
      return $ Just r
    Nothing -> do
      dlog ["election"] $ "No leader."
      return Nothing
