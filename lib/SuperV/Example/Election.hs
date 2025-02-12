-- The following GHC language extensions are used to create symbolic
-- representations of the types in this example.
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module SuperV.Example.Election where

-- Don't import anything from standard Haskell prelude, since we
-- replace several boolean operators.
import Prelude ()
import Data.Word (Word32)

-- This loads SuperV and its embedded language.
import SuperV

-----------
-- TYPES --
-----------

-- A node identifier (which is just a nat number).
newtype NodeId = NodeId Word32 deriving (Show,Eq,Ord)
-- Declare a symbolic representation for 'NodeId'.
mkDType "NodeId" ''NodeId

-- A set of nodes eligible to vote.
type Voters = Set NodeId
-- Declare a symbolic representation for sets of 'NodeID's.
mkSetMd "NodeId" ''NodeId

-- A record of votes, mapping each node that has voted to its chosen
-- candidate.
type Votes = Map NodeId NodeId
-- Declare a symbolic representation for 'NodeID' -> 'NodeId' maps.
mkMapMd "NodeId_NodeId" ''NodeId ''NodeId

-- The replicated state. Each node holds a copy.
type EState = (Voters, Votes)

-- A vote update: simply a new voter-candidate mapping.  The voter is
-- the node that produces the update, and the candidate is the node
-- identified by the update value.
type Update = (NodeId, NodeId)


--------------
-- PROTOCOL --
--------------

-- Election nodes can perform one kind of update to the replicated
-- state: issuing a vote.  This update takes effect immediately at the
-- origin node, and later takes effect at each remote node as it is
-- delivered by the network.
--
-- For every update, we define a precondition that must be checked for
-- the origin node's local state when it creates the update.  We will
-- show through verification that, as long as the runtime enforces the
-- preconditions locally, they will also hold for every remote state
-- that they are applied to.

-- This action generates a Vote update.  It returns two values: a
-- boolean indicating success, and an update value that, on success,
-- is to be issued.
voteAction :: (Avs x) => Alp x NodeId -> Alp x EState -> Alp x NodeId -> Alp x (Bool, Update)
voteAction self state cand =
  -- Unpack the state tuple using from2', binding its vote-map field
  -- as "votes".  The DSL's special representation of values prevents
  -- the use of idiomatic Haskell pattern-matching deconstruction.
  from2' state $ \_ votes ->
  -- Action is successful when the local node has not voted yet
  -- (according to its local state).
  tup2 (keyNull self votes) (tup2 self cand)

-- The handler for an update, which is used to modify the states of
-- the origin node and, eventually, all of its peers.
handleVote :: (Avs x) => Alp x Update -> Alp x EState -> Alp x EState
handleVote update state =
  from2' update $ \voter cand ->
  -- Unpack eligible voters and existing votes from the pre-state.
  from2' state $ \allVoters allVotes ->

  -- Construct the post-state,
  tup2
    -- using the same set of eligible voters,
    allVoters
    -- and adding the new vote to the existing votes.
    (insertMap voter cand allVotes)

-- The local precondition that permits issuing a vote update.
--
-- We will verify that this guard is "stable": if true for the
-- update's origin state, it must also be true for any remote state
-- that it is delivered into.  We call this condition a "Stable Update
-- Precondition (SUP)".
supVote :: (Avs x) => Alp x NodeId -> Alp x NodeId -> Alp x Update -> Alp x EState -> Alp x Bool
supVote _ self update state =
  -- Unpack existing votes from state
  from2' state $ \_ allVotes ->
  -- Check that the origin node has not yet voted.
  keyNull self allVotes
  -- And that the update's voter is the origin node
  && (fstE update == self)


-----------------
-- SAFETY SPEC --
-----------------

-- The safety condition we want to verify is that once any node
-- observes an elected leader, it will always continue to observe that
-- same elected leader.
--
-- We specify this as a "strength" preorder on node states, and verify
-- that each node's state is monotonically increasing in "strength".
strongerOrEq :: (Avs x) => Alp x NodeId -> Alp x EState -> Alp x EState -> Alp x Bool
strongerOrEq leader s1 s2 =
  isElected leader s1 ==> isElected leader s2

-- A local state query that checks if a given node has been elected as
-- the leader.
isElected :: (Avs x) => Alp x NodeId -> Alp x EState -> Alp x Bool
isElected cand state =
  from2' state $ \allVoters allVotes ->
  -- Check that the set of nodes that have voted for cand ...
  selectV cand allVotes
  -- ... is a quorum (majority) of ...
  `quorum`
  -- ... the set of all eligible voter.
  allVoters

-- This example does not require any particular integrity invariant on
-- node states.
integrity :: (Avs x) => Alp x NodeId -> Alp x EState -> Alp x Bool
integrity _ _ = trueE

-- This Template Haskell command generates the verification conditions
-- needed to verify that concurrent election updates commute, and that
-- each node is individually monotonic with respect to the strength
-- ordering.  Together, these two conditions ensure consensus safety
-- for the leader decision.
--
-- When this module is loaded in GHCI, the function 'checkAllVCs' will
-- query an SMT solver (CVC5) for each verification condition in
-- sequence, printing the results.
mkVCs
  -- Updates (name, SUP, handler, generating action)
  [("Vote", 'supVote, 'handleVote, 'voteAction)]
  -- Local integrity condition (empty in this case)
  'integrity
  -- Strength ordering, defining the safety goal
  'strongerOrEq
