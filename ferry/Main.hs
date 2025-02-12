{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

import qualified ClientComm as CC
import Config
import qualified Config.New as NC
import State
import AppState

import qualified SuperV
import Ddsl.Example.LogConsensus


import Control.Concurrent (forkIO)
import Control.Concurrent.STM
import Control.Exception (bracket)
import Control.Monad
import Control.Monad.DebugLog
import Control.Monad.State
import Data.Foldable (for_,foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import Data.Text (Text,unpack)
import qualified Data.Set as Set
import Data.Word (Word32)
import Lens.Micro.Platform
import qualified Network.Simple.TCP as TCP
import Network.Ccm (NodeId)
import qualified Network.Ccm as Ccm
import qualified Network.Ccm.Extra as Extra
import Network.Ccm.Lens
import Network.Ccm.Timer
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn,stderr)
import System.Posix (Fd)
import qualified System.Posix as PSIO

pds :: String -> IO Selector
pds s = case parseDebugSelector s of
  Right ds -> return ds
  Left e -> do
    hPutStrLn stderr $
      "Debug selector \""
      ++ s
      ++ "\" could not be parsed: "
      ++ show e
    exitFailure

main :: IO ()
main = do
  newConf <- NC.fromString . head <$> getArgs
  lvl <- mapM pds (NC.getDebugSelector newConf)
  let
    conf = NC.makeOldConfig newConf
    open = openPersist (conf^.cPersist)
    close = closePersist

  bracket open close $ \mh -> do
    flip runLogStdoutC (Set.fromList lvl) $ do
      dlog ["conf"] $ show newConf
      dlog ["conf"] $ show conf
      ctx <- CC.newCtx
      let
        server = CC.runServer
          (TCP.Host (conf^.cClientHost))
          (conf^.cClientPort)
          ctx
      liftIO . forkIO =<< passLogIO server
  
      if (conf^.cNodeId) == (conf^.cCore.cLeader)
        then runMainT leaderScript (ctx ^. CC.inputQ) conf mh
        else runMainT followerScript (ctx ^. CC.inputQ) conf mh

leaderScript :: (MonadIO m, MonadLog m) => MainT m ()
leaderScript = do
  -- Block until all peers are online/connected
  test <- lift Extra.allPeersReady
  liftIO . atomically $ check =<< test

  -- Wait until all peers are listening for app messages
  waitAllReadySignals

  forever leaderStep

-- Actually 'leaderStep' should pick from either the client message
-- queue or the peer message queue!  Probably giving priority to node
-- messages.
leaderStep
  :: (MonadIO m, MonadLog m)
  => MainT m ()
leaderStep = do
  priority <- use stPriority
  msgs <- peerOrClient priority
  stPriority %= not
  -- liftIO $ putStrLn "Priority switch"
  case msgs of
    Right inputs -> handleClientInputs inputs
    Left peerMsgs -> leaderHandle peerMsgs

handleClientInputs
  :: (MonadIO m, MonadLog m)
  => [(CC.ClientId, CC.Input)]
  -> MainT m ()
handleClientInputs inputs = do
  verboseLn $ "Handling " ++ show (length inputs) ++ " client messages."
  puts <- catMaybes <$> traverse handleClient inputs
  if not (null puts)
  then do
    let
      texts = mconcat . fmap (\(_,_,t) -> t) $ puts
      tags = Seq.fromList . fmap (\(c,sn,_) -> (c,sn)) $ puts
    -- Propose the request, getting an entry index for it
    term <- queryState () $ getBranch (SuperV.sndE SuperV.input)
    sendMsg [(SuperV.from3 proposeAction, (term, Entry $ unpack texts))]
    i <- use stIssuedProposals
    stIssuedProposals += 1
    -- Record the request and its associated index
    stPendingProposals %= (Seq.|> (i, tags))
    verboseLn $
      "Submitted a proposal combining "
      ++ show (length puts)
      ++ " requests."
  else verboseLn "No client requests this round."

handleClient
  :: (MonadIO m, MonadLog m)
  => (CC.ClientId, CC.Input)
  -> MainT m (Maybe (CC.ClientId, Csn, Text))
handleClient (client, cinput) = do
  -- If the client does not yet have a state, add one.  This makes it
  -- safe to access the client state using 'nonCheat'.
  initClient client

  case cinput of
    CC.Connect oq -> do
      stClients.at client.nonCheat.sendQ .= Just oq
      dlog ["connection"] $ "New connection from C" ++ show client

      sendStatus client
      dlog ["connection"] $ "Sent on-connection status message to C" ++ show client
      return Nothing
    CC.Disconnect -> do
      stClients.at client.nonCheat.sendQ .= Nothing
      dlog ["connection"] $ "Disconnected C" ++ show client
      return Nothing
    CC.Request (CC.RequestEntry sn t) -> do
      return $ Just (client, sn, t)
    CC.Request CC.Status -> do
      sendStatus client
      return Nothing
    CC.Request CC.Die -> do
      liftIO exitFailure

leaderHandle :: (MonadIO m, MonadLog m) => Seq FerryMsg -> MainT m ()
leaderHandle Seq.Empty = return ()
leaderHandle s = do
  let
    maxIx = foldl'
      (\i m -> case m of
          Accept (_,_,i') -> max i i'
          _ -> i)
      (Index 0)
      s

  verboseLn $ "Received " ++ show (Seq.length s) ++ " messages."
  verboseLn $ show s

  recordCommits maxIx

initClient :: (MonadState MainState m) => CC.ClientId -> m ()
initClient client = do
  cs <- use $ stClients . at client
  case cs of
    Just c -> return ()
    Nothing -> stClients . at client ?= newClientState

waitAllReadySignals :: (MonadIO m, MonadLog m) => MainT m ()
waitAllReadySignals = do
  raftMsgs <- recvMsgs
  if not $ null raftMsgs
    then error $ "Got early Raft msgs " ++ show raftMsgs ++ " in waitAllReadySignals"
    else return ()
  followers <- getFollowers <$> (use $ stConf . cCore)
  ready <- use $ stReadyFollowers
  if followers `Set.isSubsetOf` ready
    then return ()
    else waitAllReadySignals


recordCommits :: (MonadIO m, MonadLog m) => Index -> MainT m ()
recordCommits ix = do
  pending <- stPendingProposals <<.= Seq.empty
  let
    f Seq.Empty = return ()
    -- For an ix that is greater than or equal to any accept we've
    -- just received, (remember, proposal 0 is committed by Accept 1)
    f s@(ps Seq.:|> (p,es)) | p >= ix = do
      -- put p back in the pending sequence
      stPendingProposals %= ((p,es) Seq.<|)
      -- continue
      f ps
    -- For an ix < an accept we've just received,
    f s@(ps Seq.:|> (p,es)) = do
      -- Check whether it's been committed. (isCommittedB t i
      -- checks whether i entries have been committed: in other words,
      -- whether entry with index i-1 has been committed)
      com <- queryState (Branch 0, p + 1) $
        SuperV.from2 $ \args state ->
        SuperV.from2' args $ \term ix ->
        isCommittedB term ix (getAccepts state) (getQState state)
      if com
        then notifyComplete s
        else do
          -- put p back in the pending sequence
          stPendingProposals %= ((p,es) Seq.<|)
          -- continue
          f ps
  f pending

notifyComplete
  :: (MonadIO m, MonadLog m)
  => Seq (Index, Seq (CC.ClientId, Csn))
  -> MainT m ()
notifyComplete commits = do
  let
    flatten :: Seq (Index, Seq (CC.ClientId, Csn)) -> Seq (CC.ClientId, Csn)
    flatten Seq.Empty = Seq.Empty
    flatten (ps Seq.:|> (_,es)) = flatten ps <> es

    -- This recursive function collects the set of clients that should
    -- be notified and updates their 'completed' records.
    f Seq.Empty clients = return clients
    f (ps Seq.:|> (c,n)) clients | not $ Set.member c clients = do
      -- Update 'completed' for client to n.
      oldVal <- use $ stClients.at c.nonCheat.clientCompleted
      newVal <- stClients.at c.nonCheat.clientCompleted <.= (n + 1)
      verboseLn $
        "Updated C" ++ show c
        ++ " from " ++ show oldVal
        ++ " to " ++ show newVal
      -- Mark that we're going to notify client 'c'.
      f ps (Set.insert c clients)
    -- If we already marked the client for an entry, we ignore it,
    -- since it must have a lower sequence-number than the one we
    -- already saw.
    f (ps Seq.:|> p) clients = f ps clients
  clients <- f (flatten commits) Set.empty
  for_ clients $ \c -> sendStatus c

sendStatus :: (MonadIO m, MonadLog m) => CC.ClientId -> MainT m ()
sendStatus c = do
  count <- use $ stClients.at c.nonCheat.clientCompleted
  use (stClients.at c.nonCheat.sendQ) >>= \case
    Just sq -> CC.writeQ sq (CC.Completed count)
    Nothing -> dlog ["error"] $
      "Client C"
      ++ show c
      ++ " not connected, could not give status"

followerScript :: (MonadIO m, MonadLog m) => MainT m ()
followerScript = do
  -- Block until all peers are online/connected
  test <- lift Extra.allPeersReady
  liftIO . atomically $ check =<< test

  sendReadySignal

  startElectionTimer

  forever followerStep
    -- sendEndSignal
    -- lift $ atomicallyCcm awaitAllSent
    -- waitAllEnded
    -- use stDeferrals

-- If any fresh votes have been received, vote and return 'True'.
tryVote :: (MonadIO m, MonadLog m) => Branch -> Seq FerryMsg -> MainT m Bool
tryVote _ Seq.Empty = return False
tryVote prev (Vote (t,_,i) Seq.:<| ms) | t >= prev = do
  sendMsg [(SuperV.from3 voteAction, (t,i))]
  -- stLeader .= Just (r2n i)
  startElectionTimer
  return True
tryVote prev (_ Seq.:<| ms) = tryVote prev ms

followerStep :: (MonadIO m, MonadLog m) => MainT m ()
followerStep = do
  prevNextBranch <- nextFreshBranch
  priority <- use stPriority
  msgs <- peerOrClientOrTimer priority
  stPriority %= not
  case msgs of
    Just (Right inputs) -> for_ inputs followerHandleClient
    Just (Left peerMsgs) -> do
      vResult <- tryVote prevNextBranch peerMsgs
      if vResult
        then forever voterStep
        else do
          let
            anyPropose = any $ \m -> case m of
              Propose _ -> True
              _ -> False
    
          verboseLn $ "Received " ++ show (length peerMsgs) ++ " messages."
          verboseLn $ show msgs
          case peerMsgs of
            ms | null ms -> return ()
            ms | anyPropose ms -> do
              sendMsg [(SuperV.from3 acceptAction, ())]
            _ -> return ()
    -- 'Nothing' indicates that the leader timer has expired
    Nothing -> do
      runForElection
      forever voterStep

runForElection :: (MonadIO m, MonadLog m) => MainT m ()
runForElection = do
  -- Remove leader
  stLeader .= Nothing
  stLeaderTimer .= Nothing

  -- Annouce to clients that leader has been lost
  clientBroadcast CC.NoLeader

  -- Run for election
  selfRid <- icSelf
  term <- nextFreshBranch
  sendMsg [(SuperV.from3 voteAction, (term,selfRid))]
  -- stLeader .= Just (r2n selfRid)
  startElectionTimer
  dlog ["election"] $ "Ran for election."

voterStep :: (MonadIO m, MonadLog m) => MainT m ()
voterStep = do
  prevNextBranch <- nextFreshBranch
  priority <- use stPriority
  msgs <- peerOrClientOrTimer priority
  stPriority %= not
  case msgs of
    Just (Right inputs) -> for_ inputs followerHandleClient
    Just (Left peerMsgs) -> do
      result <- checkForLeader
      case result of
        Just rid -> do
          clientBroadcast $ CC.LeaderIs rid
          forever (peerOrClientOrTimer priority >> return ())
        Nothing -> do
          tryVote prevNextBranch peerMsgs
          return ()
    -- 'Nothing' indicates that the leader timer has expired
    Nothing -> do
      runForElection

followerHandleClient
  :: (MonadIO m, MonadLog m)
  => (CC.ClientId, CC.Input)
  -> MainT m ()
followerHandleClient (client, cinput) = do
  -- If the client does not yet have a state, add one.  This makes it
  -- safe to access the client state using 'nonCheat'.
  initClient client

  case cinput of
    CC.Connect oq -> do
      stClients.at client.nonCheat.sendQ .= Just oq
      dlog ["connection"] $ "New connection from C" ++ show client
    CC.Disconnect -> do
      stClients.at client.nonCheat.sendQ .= Nothing
      dlog ["connection"] $ "Disconnected C" ++ show client
    _ -> dlog ["error"] $
      "Follower got client request for a leader: "
      ++ show (client, cinput)

openPersist
  :: (MonadIO m)
  => Maybe FilePath
  -> m (Maybe Fd)
openPersist Nothing = return Nothing
openPersist (Just fp) = fmap Just . liftIO $
  PSIO.createFile
    fp
    (PSIO.unionFileModes PSIO.ownerReadMode PSIO.ownerWriteMode)

closePersist
  :: (MonadIO m)
  => Maybe Fd
  -> m ()
closePersist Nothing = return ()
closePersist (Just f) = liftIO . PSIO.closeFd $ f
