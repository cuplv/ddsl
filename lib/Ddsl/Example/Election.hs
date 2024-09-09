-- The following GHC language extensions are used to create symbolic
-- representations of the types in this example.
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Example.Election where

-- This loads the Ddsl embedded language.
import Ddsl.Prelude

-- Don't import everything from standard Haskell prelude, since we
-- replace several boolean operators.
import Prelude (print,putStr,(=<<))


-----------
-- TYPES --
-----------

-- A node identifier (which is just an 'Int').
data NodeId = NodeId Int deriving (Show,Eq,Ord)
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
type Update = NodeId


--------------
-- PROTOCOL --
--------------

-- Election nodes can perform one kind of update to the replicated
-- state: issuing a vote.  This update takes effect immediately at the
-- origin node, and later takes effect at each remote node as it is
-- delivered by the network.
--
-- For every update, we define a precondition that must hold for the
-- origin node's local state when it creates the update.  We will show
-- through verification that, as long as the runtime enforces the
-- preconditions locally, they will also hold for every remote state
-- that they are applied to.

-- The effect of an update.  The first 'NodeId' argument is the origin
-- node that produced the update.
--
-- The 'Df3' type is the type of Ddsl functions with 3 arguments.
updateEffect :: Df3 NodeId Update EState EState
updateEffect voter cand state =
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
-- We will verify that this guard, if true for the update's origin
-- state, must also be true for any remote state that it is delivered
-- into.
updatePre :: Df3 NodeId Update EState Bool
updatePre voter cand state =
  -- Unpack existing votes from state
  from2' state $ \_ allVotes ->
  -- Check that the voter has not yet voted.
  keyNull voter allVotes


-----------------
-- SAFETY SPEC --
-----------------

-- The safety condition we want to verify is that once any node
-- observes an elected leader, it will always continue to observe that
-- same elected leader.
--
-- We specify this as a preorder 'monoLeader' on node states, and
-- verify that each node's state is monotonically increasing according
-- to that preorder.
monoLeader :: Df3 NodeId EState EState Bool
monoLeader leader s1 s2 =
  isElected leader s1 ==> isElected leader s2

-- A local state query that checks if a given node has been elected as
-- the leader.
isElected :: Df2 NodeId EState Bool
isElected cand state =
  from2' state $ \allVoters allVotes ->
  -- Check that the set of nodes that have voted for cand ...
  selectV cand allVotes
  -- ... is a quorum (majority) of ...
  `quorum`
  -- ... the set of all eligible voter.
  allVoters


-----------------------------
-- VERIFICATION CONDITIONS --
-----------------------------

-- Check that the monotonicity relation is reflexive.
--
-- The 'Df' type is the type of Ddsl functions with one argument.  A
-- single-function argument with 'Bool' serves as a verification
-- condition, where the argument is universally quantified and the
-- condition is verified iff the result is always 'True'.
vc1 :: Df (NodeId, EState) Bool
vc1 args =
  from2' args $ \leader s ->
  monoLeader leader s s

-- Check that the monotonicity relation is transitive.
--
-- Being reflexive and transitive, 'monoLeader' is thus a preorder.
vc2 :: Df (NodeId, (EState, EState, EState)) Bool
vc2 args =
  from2' args $ \leader states ->
  from3' states $ \s1 s2 s3 ->
  (monoLeader leader s1 s2
   && monoLeader leader s2 s3)
  ==> monoLeader leader s1 s3

-- Check that the monotonicity relation is upheld by every update that
-- is valid (precondition-satisfying).
vc3 :: Df (NodeId, (NodeId, Update, EState)) Bool
vc3 args =
  from2' args $ \leader ps ->
  from3' ps $ \voter cand state1 ->
  let
    state2 = updateEffect voter cand state1
  in
    -- Assume that the update is valid.
    updatePre voter cand state1
    -- Show that the change satisfies the monotonicity property.
    ==> monoLeader leader state1 state2

-- Check that every update's precondition is "strong": that it is
-- preserved by any other update that is valid
-- (precondition-satisfying) and concurrent (distinct origin node).
vc4 :: Df (NodeId, (NodeId, Update, NodeId, Update, EState)) Bool
vc4 args =
  from2' args $ \leader ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = updateEffect origin2 update2 state1
    -- We are checking that this condition is not invalidated by the
    -- effect of update2.
    pre1 = updatePre origin1 update1
  in
    -- Assume that update2 is valid in state1 (its precondition
    -- holds),
    (updatePre origin2 update2 state1
    -- and that update2 is concurrent with update1 (they have
    -- distinct origin nodes).
    && (origin1 /= origin2))
    -- Show that update1's precondition is not invalidated by update2.
    ==> (pre1 state1 ==> pre1 state2)

-- Check that updates always commute when they are valid
-- (precondition-satisfying) and concurrent (distinct origin nodes).
vc5 :: Df (NodeId, Update, NodeId, Update, EState) Bool
vc5 args =
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      updateEffect origin2 update2
        (updateEffect origin1 update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      updateEffect origin1 update1
        (updateEffect origin2 update2 state)
  in
    -- Assume that the updates are valid,
    (updatePre origin1 update1 state
    && updatePre origin2 update2 state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

-- Put the conditions all together.  The 'verify' function takes a
-- verification condition (single-argument function with boolean
-- output) and checks that it is valid (its negation is unsatisfiable)
-- using an SMT solver.
verifyElection :: IO ()
verifyElection = do
  putStr "VC #1 (reflexive).  "
  print =<< verify vc1
  putStr "VC #2 (transitive). "
  print =<< verify vc2
  putStr "VC #3 (monotonic).  "
  print =<< verify vc3
  putStr "VC #4 (strong).     "
  print =<< verify vc4
  putStr "VC #5 (commutable). "
  print =<< verify vc5
