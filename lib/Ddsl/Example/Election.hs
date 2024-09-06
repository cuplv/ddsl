{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Example.Election where

import Ddsl.Prelude

-- Don't import everything from standard Haskell prelude, since we
-- replace several boolean operators.
import Prelude (print,putStr,(=<<))

data NodeId = NodeId Int deriving (Show,Eq,Ord)
mkDType "NodeId" ''NodeId
mkSetMd "NodeId" ''NodeId

type VoteMap = Map NodeId NodeId

mkMapMd "NodeId_NodeId" ''NodeId ''NodeId


-- A set of replicas eligible to vote.
type Voters = Set NodeId
-- A map of each replica that has voted to its chosen candidate.
type Votes = Map NodeId NodeId
-- The replicated state. Each replica holds a copy.
type EState = (Voters, Votes)
-- A vote message: simply a new voter-candidate mapping.
type VoteMsg = (NodeId, NodeId)

{- | A local state query that checks if a given replica has been
   elected. -}
isElected :: Df2 NodeId EState Bool
isElected cand state =
  from2' state $ \allVoters allVotes ->
  quorum
    -- The set of nodes that have voted for cand ...
    (selectV cand allVotes)
    -- ... includes a quorum of the nodes eligible to vote.
    allVoters

voteGen :: Df3 NodeId EState NodeId (Bool, VoteMsg)
voteGen self state cand =
  keyNull self (sndE state)
  &&& (tup2 self cand)

voteGenTest :: Df ((NodeId,EState,NodeId),(NodeId)) Bool
voteGenTest args =
  from2' args $ \concrete abstract ->
  from3' concrete $ \self state arg ->
  letb (voteGen self state arg) $ \result ->
  from2' result $ \ok msg ->

  (ok) $=>
  (voteGuard abstract self msg state)

{- | The effect of the vote message.

   This is used to modify the origin replica's state, as well as the
   states of every replica that the message is delivered to. -}
voteEffect :: Df2 VoteMsg EState EState
voteEffect msg state =
  -- Unpack voter and cand from msg
  from2' msg $ \voter cand ->
  -- Unpack eligible voters and existing votes from state
  from2' state $ \allVoters allVotes ->

  -- Construct the post-state tuple
  tup2
    -- Using the same set of eligible voters
    allVoters
    -- And the new vote added to the existing votes
    (insertMap voter cand allVotes)


{- | The local guard that permits issuing a vote message.

   We will verify that this guard, if true for the message's origin
   state, must also be true for any remote state that it is delivered
   into. -}
voteGuard :: Df4 NodeId NodeId VoteMsg EState Bool
voteGuard _ selfId myMsg myState =
  -- Unpack voter and cand from msg
  from2' myMsg $ \voter cand ->
  -- Unpack eligible voters and existing votes from state
  from2' myState $ \allVoters allVotes ->

  -- Check that the replica is voting in its own name
  (voter == selfId)
  -- And that it has not yet voted
  && keyNull selfId allVotes


{- | The safety goal is a relation on two states, which requires that
   the two states do not witness two different replicas having been
   elected.  This is an example of a consensus property.

   The goal property is written with respect to an arbitrary pair of
   replica IDs, which are universally quantified for verification. -}
safetyGoal :: Df3 (NodeId,NodeId) EState EState Bool
safetyGoal rids s1 s2 =
  from2' rids $ \r1 r2 ->

  -- It is not the case that ...
  not $
    -- ... r1 and r2 are different replicas and ...
    (r1 /= r2)
    -- ... one has been elected in the first state ...
    && isElected r1 s1
    -- ... while the other has been elected in the second state.
    && isElected r2 s2

goal :: Df3 NodeId EState EState Bool
goal _ s1 s2 =
  (fstE s1 == fstE s2)
  && (sndE s1 `submap` sndE s2)

{- | The guarantee is also a relation on two states, but takes a
   "subnet" parameter (a set of replica IDs) as well.  The guarantee
   constrains the state changes that the members of the subnet are
   allowed to make, as group. -}
guarantee :: (Avs x) => Alp x (NodeId,NodeId) -> Alp x (Set NodeId) -> Alp x EState -> Alp x EState -> Alp x Bool
guarantee rids subnet s1 s2 =
  -- The guarantee is written with respect to the same arbitrary pair
  -- of replica IDs that the safetyGoal refers to.  We will only
  -- constrain one of them.
  from2' rids $ \r1 _ ->

  -- Election of the arbitrary candidate is preserved, ...
  (isElected r1 s1 ==> isElected r1 s2)
  -- ... and there are no new votes attributed to any replica which is
  -- not a member of the given subnet.
  && (unauthorizedVotes == emptyMap)

  where
    unauthorizedVotes =
      from2' s1 $ \_ votes1 ->
      from2' s2 $ \_ votes2 ->

      -- Employ a user-defined map filter.
      filterMap
        -- (Give a unique name for the generated uninterpreted
        -- function.  This could be automated away with some
        -- engineering work.)
        "unauthorizedVotes"
        -- Given the subnet and the first state's votes ...
        (tup2 subnet votes1)
        -- ... collect all votes from the second state ...
        votes2
        -- ... that are "unauthorized", meaning: ...
        (\args k v ->
           from2' args $ \subnet votes1 ->
           -- ... a vote which is new (not in first state) ...
           not (keyVal k v votes1)
           -- ... and attributed to a voter that is not in the subnet.
           && not (member k subnet))

vc1 :: Df (NodeId, EState) Bool
vc1 args =
  from2' args $ \arg s ->
  goal arg s s

vc2 :: Df (NodeId, (EState, EState, EState)) Bool
vc2 args =
  from2' args $ \arg states ->
  from3' states $ \s1 s2 s3 ->
  (goal arg s1 s2 && goal arg s2 s3)
  ==> goal arg s1 s3

vc3 :: Df (NodeId, (NodeId, VoteMsg, EState)) Bool
vc3 args =
  from2' args $ \arg ps ->
  from3' ps $ \r m s ->
  voteGuard arg r m s
  ==> goal arg s (voteEffect m s)

vc4 :: Df (NodeId, (NodeId, VoteMsg, NodeId, VoteMsg, EState)) Bool
vc4 args =
  from2' args $ \arg ps ->
  from5' ps $ \r1 m1 r2 m2 s ->
  ((r1 /= r2)
  && voteGuard arg r1 m1 s
  && voteGuard arg r2 m2 s)
  ==> voteGuard arg r2 m2 (voteEffect m1 s)

vc5 :: Df (NodeId, (NodeId, VoteMsg, NodeId, VoteMsg, EState)) Bool
vc5 args =
  from2' args $ \arg ps ->
  from5' ps $ \r1 m1 r2 m2 s ->
  letb (voteEffect m2 (voteEffect m1 s)) $ \s1 ->
  letb (voteEffect m1 (voteEffect m2 s)) $ \s2 ->

  ((r1 /= r2)
  && voteGuard arg r1 m1 s
  && voteGuard arg r2 m2 s)
  ==> (s1 == s2)

vc6 :: Df (NodeId, NodeId, (EState, EState, EState)) Bool
vc6 args =
  from3' args $ \arg1 arg2 ps ->
  from3' ps $ \s1 s2 s3 ->
  (goal arg1 s1 s3
  && goal arg1 s2 s3
  && goal arg2 s1 s3
  && goal arg2 s2 s3)
  ==> safetyGoal (tup2 arg1 arg2) s1 s2

verifyElection conf = do
  putStr "VC #1. "
  print =<< verify' conf vc1
  putStr "VC #2. "
  print =<< verify' conf vc2
  putStr "VC #3. "
  print =<< verify' conf vc3
  putStr "VC #4. "
  print =<< verify' conf vc4
  putStr "VC #5. "
  print =<< verify' conf vc5
  putStr "VC #6. "
  print =<< verify' conf vc6
  putStr "VC #7. "
  print =<< verify' conf voteGenTest
