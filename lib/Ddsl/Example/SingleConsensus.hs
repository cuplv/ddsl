{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

{- | This is a consenus algorithm for a single decision value, similar
   to single-decree Paxos.

   The safety property, 'monoValue', ensures that once a node has
   observed a decided value, it will continue to observe that same
   decided value.  Combined with the convergence property, this gives
   us the standard Paxos consensus safety property.
-}
module Ddsl.Example.SingleConsensus where

import Ddsl.Prelude

import Prelude (print,putStr,(=<<),Num,String)

-----------
-- TYPES --
-----------

-- A node identifier (which is just an 'Int').
newtype NodeId = NodeId Int deriving (Show,Eq,Ord)
-- Declare an opaque symbolic representation for 'NodeId'.
mkDType "NodeId" ''NodeId

-- A term (also just an 'Int').
newtype Term = Term Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Term'.
mkNatMd "Term" ''Term
-- We'll reason about sets of terms, so we declare this as well.
mkSetMd "Term" ''Term

-- A set of nodes eligible to vote.
type Voters = Set NodeId
-- Declare a symbolic representation for sets of 'NodeID's.
mkSetMd "NodeId" ''NodeId

-- A voting node in a particular term
type VoterId = (Term,NodeId)
-- A record of votes
type Votes = Map VoterId NodeId
-- Declare a symbolic representation for the Votes map.
mkMapMd "TermRid_Rid" ''VoterId ''NodeId

-- A decision value
newtype Value = Value String deriving (Show,Eq,Ord)
mkDType "Value" ''Value

-- A record of accepts for the decision values proposed in particular
-- terms.
type Accepts = Set VoterId
mkSetMd "Term_NodeId" ''VoterId

-- A 'Rejecter' is a witness that certain terms' values can no longer
-- be accepted.  It consists of a quorum-size 'Voters' set and a
-- 'Term' that they have all voted in.  This means that the voters are
-- not allowed to make new accepts for any older term, and so any
-- older term that none have accepted can no longer gather a quorum of
-- accepters.
type Rejecter = (Term, Voters)
-- This is required for the 'nonePassSet' quantification in
-- 'rejecterExists'.
mkSetMd "Rejecter" ''Rejecter

-- We declare a single manual quantifier alternaton edge, from the
-- given tuple type to the 'NodeId' type.
--
-- Automatic quantifier alternation edges are created from Sets and
-- Maps to their elements.
--
-- Note that manually-declared quantifier alternation edges are NOT
-- checked for conflicts: as far as I know, doing so is not possible
-- with Haskell's typeclass system.  To avoid defining conflicting
-- edges, declare all edges in one place in your source file.
instance QE (Rejecter, Term, Votes, Accepts) NodeId

-- The state of a SingleConsensus node is has the following parts:
--
-- 1. The set of eligible voters, which does not change over the
-- course of the execution.
--
-- 2. The map of vote records.
--
-- 3. The proposal state, with three parts:
--
--   3.1 Ddsl does not have Maybe/Sum types, so we use a Bool flag to
--   mark whether the proposal values should be considered a real
--   proposal, or considered "uninitialized".
--
--   3.2 The term of the latest proposal (if any).
--
--   3.3 The value of the latest proposal (if any).
--
-- 4. The set of accept records.
type State = (Voters, Votes, (Bool, Term, Value), Accepts)

-- An Accept update simply includes the proposal term that the origin
-- node is accepting.
type AcceptU = Term

--------------
-- PROTOCOL --
--------------

-- There are three kinds of updates.
--
-- First, a Vote update records a vote for a candidate node for a
-- particular term.
--
-- Second, a Propose update advances the current term and sets a
-- proposed value.
--
-- Third, an Accept update records a node's acknowledgment of the
-- proposed value for a given term.

-- The precondition for Vote updates
votePre :: Df3 NodeId VoteU State Bool
votePre origin update state =
  from4' state $ \_ vs _ as ->
  from2' update $ \term cand ->
  -- Check that origin has not yet voted in this term,
  keyNull (tup2 term origin) vs
  -- and that origin has not yet accepted in this or any future
  -- term.
  && (nonePassSet "votePre" (tup2 term origin) as $
    \args accept ->
    from2' args $ \vTerm vNode ->
    from2' accept $ \aTerm aNode ->
    (aTerm >= vTerm)
    && (aNode == vNode))

-- The effect of Vote updates
voteEffect :: Df3 NodeId VoteU State State
voteEffect origin update state =
  from2' update $ \term cand ->
  -- Modify the Votes field ...
  tup4m2 state $
    -- ... by inserting the new vote.
    insertMap (tup2 term origin) cand

-- A Propose update consists of the proposal term (which the origin
-- must be elected leader for) and the proposal value.
type ProposeU = (Term, Value)

-- The precondition for Propose updates.  Note that this precondition
-- takes an arbitrary Term argument, which is universally quantified
-- in the verification conditions.
proposePre :: Df4 Term NodeId ProposeU State Bool
proposePre uniTerm origin update state =
  from4' state $ \ev vs cr as ->
  from3' cr $ \isSet cTerm cVal ->
  from2' update $ \pTerm pVal ->
  -- Check that origin is elected for the proposal term,
  isElected pTerm origin (tup2 ev vs)
  -- and that no invalid accepts exist,
  && acceptRule state
  -- and that, if the proposal term exceeds the current term, then
  -- either ...
  && ((pTerm >= cTerm) ==>
    -- ... no actual proposal has been made, or
    (not isSet
    -- the proposal value matches the current value, or
    || (pVal == cVal)
    -- any term previous to our proposal term (including the current
    -- term) has been rejected by the voters of a completed leader
    -- election.
    || ((pTerm > uniTerm) ==> rejecterExists uniTerm state)))

acceptRule :: Df State Bool
acceptRule state =
  from4' state $ \_ _ cr as ->
  from3' cr $ \pr cTerm _ ->
  -- No accepts should exist before a first proposal has been made,
  (not pr ==> isEmptySet as)
  -- and no accepts' terms should exceed the latest-proposed term.
  && (nonePassSet "acceptRule" cTerm as $
    \cTerm a ->
    from2' a $ \aTerm _ ->
    aTerm > cTerm)

isElected :: Df3 Term NodeId (Voters, Votes) Bool
isElected term cand state =
  from2' state $ \allVoters allVotes ->
  -- Check that the set of nodes that have voted for cand in term ...
  selectFst term (selectV cand allVotes)
  -- ... is a quorum (majority) of ...
  `quorum`
  -- ... the set of all eligible voters.
  allVoters

-- Check that a Rejecter witness exists for the given Term.
rejecterExists :: Df2 Term State Bool
rejecterExists aTerm state =
  from4' state $ \ev vs _ as ->
  -- aTerm is rejected if some Rejecter value exists that passes the
  -- 'isRejecter' test for aTerm:
  --
  -- Check that it is not true ...
  not $
    -- ... that no member of the 'fullSet' of all possible Rejecter
    -- values ...
    nonePassSet "rejecterExists" (tup4 aTerm ev vs as) fullSet $
      -- ... satisfies the following predicate:
      \args rj ->
      from4' args $ \aTerm ev vs as ->
      isRejecter rj aTerm ev vs as
  --
  -- Higher-order functions like 'nonePassSet' have a couple of
  -- oddities.
  --
  -- First, you must give it a unique symbol name, which will be used
  -- to create the underlying SMT symbol.  Here, we use
  -- "rejecterExists".
  --
  -- Second, you can't use values from the surrounding scope in the
  -- predicate function: you must pass in the values you want to use
  -- explicitly.  Here, we explicitly pass in @(tup4 aTerm ev vs as)@,
  -- which gets bound to 'args'.  If you try to use values from the
  -- surrounding scope, you'll get a confusing type error.

isRejecter :: Df5 Rejecter Term Voters Votes Accepts Bool
isRejecter rj t ev vs as =
  from2' rj $ \rTerm rVoters ->
  -- rj is a rejecter for t only if...
  --
  -- rj's term is greater than t,
  (rTerm > t)
  -- and rj's voters are a quorum,
  && quorum rVoters ev
  -- and each of rj's voters meet the following conditions:
  --
  -- (this function universally quantifies over all 'NodeId's in the
  -- context of the explicit arguments @(tup4 rj t vs as)@, and so we
  -- had to define the 'QE' quanfier edge at the top of the file)
  && (universal "isRejecter" (tup4 rj t vs as) $
    \args voter ->
    from4' args $ \rj t vs as ->
    from2' rj $ \rTerm rVoters ->
    member voter rVoters ==>
      -- each voter has not accepted term t,
      (not (member (tup2 t voter) as)
      -- and each voter has voted in rj's term.
      && not (keyNullPart (tup2 rTerm voter) vs)))

-- The effect of Propose updates
proposeEffect :: Df3 NodeId ProposeU State State
proposeEffect origin update state =
  from4' state $ \_ _ cr _ ->
  from3' cr $ \pr cTerm _ ->
  from2' update $ \pTerm pVal ->

  ite
    -- If the proposal term exceeds the current term,
    ((pTerm > cTerm)
    -- or no proposal has been made,
    || not pr)

    -- then update the state,
    (tup4m3 state $
      -- Set "proposal exists" to True, set the current term to the
      -- proposal term, and set the current value to the proposal value.
      \_ -> tup3 trueE pTerm pVal)

    -- else leave it unchanged.
    state

-- A Vote update consists of the term in which voting is taking place,
-- and the candidate that is being voted for (by the update's origin
-- node).
type VoteU = (Term, NodeId)

-- The precondition for Accept updates
acceptPre :: Df3 NodeId AcceptU State Bool
acceptPre origin update state =
  from4' state $ \_ vs cr as ->
  from3' cr $ \pr cTerm _ ->
  -- Check that a proposal exists,
  pr
  -- the current term meets or exceeds the accepting term,
  && (cTerm >= update)
  -- -- and the origin has not yet voted in any future term.
  && (nonePassSet "acceptPre2" (tup3 origin update vs) fullSet $
    \args someTerm ->
    from3' args $ \origin aTerm vs ->
    (someTerm > aTerm)
    -- 'keyNullPart' asserts that the key has no value in the map.
    && not (keyNullPart (tup2 someTerm origin) vs))

-- The effect of Accept updates
acceptEffect :: Df3 NodeId AcceptU State State
acceptEffect origin update state =
  tup4m4 state $
    -- Insert the accepting term and the accepting node.
    insertSet (tup2 update origin)


-----------------
-- SAFETY SPEC --
-----------------

-- If a node observes a given value as decided, then it will continue
-- to observe this value as decided in the future.
monoValue :: Df3 (Term,Value) State State Bool
monoValue args s1 s2 =
  from2' args $ \term value -> 
  isDecided term value s1 ==> isDecided term value s2

-- A value is "decided" when it is identical to the latest proposed
-- value, and a quorum of eligible voters have accepted the latest
-- term.
isDecided :: Df3 Term Value State Bool
isDecided term value s =
  from4' s $ \ev _ cr as ->
  from3' cr $ \pr tm vl ->
  let
    -- Collect the set of nodes that have accepted the latest term,
    accepters =
      -- by filtering the set of eligible voters.
      filterSet "accepters" (tup2 term as) ev $
        -- For each eligible voter,
        \args node ->
        from2' args $ \aTerm accepts ->
        -- check for a record of it accepting the latest term.
        member (tup2 aTerm node) accepts
  in
    -- Check that the given value is identical to the latest proposed
    -- value,
    value == vl
    -- and that the given term is not greater than the latest proposal
    -- term,
    && (tm >= term)
    -- and that the given term has been quorum-accepted,
    && quorum accepters ev
    -- and that a proposal exists in the first place.
    && pr


-----------------------------
-- VERIFICATION CONDITIONS --
-----------------------------

-- Check that the monotonicity relation is reflexive.
vc1 :: Df ((Term,Value), State) Bool
vc1 args =
  from2' args $ \value s ->
  monoValue value s s

-- Check that the monotonicity relation is transitive.
vc2 :: Df ((Term,Value), (State, State, State)) Bool
vc2 args =
  from2' args $ \value states ->
  from3' states $ \s1 s2 s3 ->
  (monoValue value s1 s2
   && monoValue value s2 s3)
  ==> monoValue value s1 s3

-- Check that every valid Vote update satisfies the monotonicity
-- relation.  We will check the same thing for the Propose and Accept
-- updates.
vc3Vo :: Df ((Term,Value), (NodeId, VoteU, State)) Bool
vc3Vo args =
  from2' args $ \value ps ->
  from3' ps $ \origin update state1 ->
  let
    state2 = voteEffect origin update state1
  in
    -- Assume that the update is valid.
    votePre origin update state1
    -- Show that the change satisfies the monotonicity property.
    ==> monoValue value state1 state2

vc3Pr :: Df ((Term,Value), (NodeId, ProposeU, State)) Bool
vc3Pr args =
  from2' args $ \uni ps ->
  from2' uni $ \term _ ->
  from3' ps $ \origin update state1 ->
  let
    state2 = proposeEffect origin update state1
  in
    proposePre term origin update state1
    ==> monoValue uni state1 state2

vc3Ac :: Df ((Term,Value), (NodeId, AcceptU, State)) Bool
vc3Ac args =
  from2' args $ \uni ps ->
  from2' uni $ \term _ ->
  from3' ps $ \origin update state1 ->
  let
    state2 = acceptEffect origin update state1
  in
    acceptPre origin update state1
    ==> monoValue uni state1 state2

-- Check that every update's precondition is "strong": that it is
-- preserved by any other update that is valid
-- (precondition-satisfying) and concurrent (distinct origin node).
--
-- We must perform this check for every combination of possible
-- updates, in every order, so there are 9 total instances of this
-- condition.
vc4VoVo :: Df ((Term,Value), (NodeId, VoteU, NodeId, VoteU, State)) Bool
vc4VoVo args =
  from2' args $ \_ ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = voteEffect origin2 update2 state1
    pre1 = votePre origin1 update1
  in
    (votePre origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4PrVo :: Df ((Term,Value), (NodeId, VoteU, NodeId, ProposeU, State)) Bool
vc4PrVo args =
  from2' args $ \uni ps ->
  from2' uni $ \uniTerm _ ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = proposeEffect origin2 update2 state1
    pre1 = votePre origin1 update1
  in
    (proposePre uniTerm origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4AcVo :: Df ((Term,Value), (NodeId, VoteU, NodeId, AcceptU, State)) Bool
vc4AcVo args =
  from2' args $ \_ ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = acceptEffect origin2 update2 state1
    pre1 = votePre origin1 update1
  in
    (acceptPre origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4VoPr :: Df ((Term,Value), (NodeId, ProposeU, NodeId, VoteU, State)) Bool
vc4VoPr args =
  from2' args $ \uni ps ->
  from2' uni $ \uniTerm _ ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = voteEffect origin2 update2 state1
    pre1 = proposePre uniTerm origin1 update1
  in
    (votePre origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4PrPr :: Df ((Term,Value), (NodeId, ProposeU, NodeId, ProposeU, State)) Bool
vc4PrPr args =
  from2' args $ \uni ps ->
  from2' uni $ \uniTerm _ ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = proposeEffect origin2 update2 state1
    pre1 = proposePre uniTerm origin1 update1
  in
    (proposePre uniTerm origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4AcPr :: Df ((Term,Value), (NodeId, ProposeU, NodeId, AcceptU, State)) Bool
vc4AcPr args =
  from2' args $ \uni ps ->
  from2' uni $ \uniTerm _ ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = acceptEffect origin2 update2 state1
    pre1 = proposePre uniTerm origin1 update1
  in
    (acceptPre origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4VoAc :: Df ((Term,Value), (NodeId, AcceptU, NodeId, VoteU, State)) Bool
vc4VoAc args =
  from2' args $ \_ ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = voteEffect origin2 update2 state1
    pre1 = acceptPre origin1 update1
  in
    (votePre origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4PrAc :: Df ((Term,Value), (NodeId, AcceptU, NodeId, ProposeU, State)) Bool
vc4PrAc args =
  from2' args $ \uni ps ->
  from2' uni $ \uniTerm _ ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = proposeEffect origin2 update2 state1
    pre1 = acceptPre origin1 update1
  in
    (proposePre uniTerm origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4AcAc :: Df ((Term,Value), (NodeId, AcceptU, NodeId, AcceptU, State)) Bool
vc4AcAc args =
  from2' args $ \_ ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = acceptEffect origin2 update2 state1
    pre1 = acceptPre origin1 update1
  in
    (acceptPre origin2 update2 state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

-- Check that every pair of valid updates commute.
--
-- We must check this for every combinataion of updates, but it is
-- un-ordered, so there are 6 total instances of this condition.
vc5VoVo :: Df ((Term,Value), (NodeId, VoteU, NodeId, VoteU, State)) Bool
vc5VoVo x =
  from2' x $ \_ args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      voteEffect origin2 update2
        (voteEffect origin1 update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      voteEffect origin1 update1
        (voteEffect origin2 update2 state)
  in
    -- Assume that the updates are valid,
    (votePre origin1 update1 state
    && votePre origin2 update2 state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5VoPr :: Df ((Term,Value), (NodeId, VoteU, NodeId, ProposeU, State)) Bool
vc5VoPr x =
  from2' x $ \uni args ->
  from2' uni $ \uniTerm _ ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      proposeEffect origin2 update2
        (voteEffect origin1 update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      voteEffect origin1 update1
        (proposeEffect origin2 update2 state)
  in
    -- Assume that the updates are valid,
    (votePre origin1 update1 state
    && proposePre uniTerm origin2 update2 state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5VoAc :: Df ((Term,Value), (NodeId, VoteU, NodeId, AcceptU, State)) Bool
vc5VoAc x =
  from2' x $ \_ args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      acceptEffect origin2 update2
        (voteEffect origin1 update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      voteEffect origin1 update1
        (acceptEffect origin2 update2 state)
  in
    -- Assume that the updates are valid,
    (votePre origin1 update1 state
    && acceptPre origin2 update2 state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5PrPr :: Df ((Term,Value), (NodeId, ProposeU, NodeId, ProposeU, State)) Bool
vc5PrPr x =
  from2' x $ \uni args ->
  from2' uni $ \uniTerm _ ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      proposeEffect origin2 update2
        (proposeEffect origin1 update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      proposeEffect origin1 update1
        (proposeEffect origin2 update2 state)
  in
    -- Assume that the updates are valid,
    (proposePre uniTerm origin1 update1 state
    && proposePre uniTerm origin2 update2 state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5PrAc :: Df ((Term,Value), (NodeId, ProposeU, NodeId, AcceptU, State)) Bool
vc5PrAc x =
  from2' x $ \uni args ->
  from2' uni $ \uniTerm _ ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      acceptEffect origin2 update2
        (proposeEffect origin1 update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      proposeEffect origin1 update1
        (acceptEffect origin2 update2 state)
  in
    -- Assume that the updates are valid,
    (proposePre uniTerm origin1 update1 state
    && acceptPre origin2 update2 state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5AcAc :: Df ((Term,Value), (NodeId, AcceptU, NodeId, AcceptU, State)) Bool
vc5AcAc x =
  from2' x $ \_ args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      acceptEffect origin2 update2
        (acceptEffect origin1 update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      acceptEffect origin1 update1
        (acceptEffect origin2 update2 state)
  in
    -- Assume that the updates are valid,
    (acceptPre origin1 update1 state
    && acceptPre origin2 update2 state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

-- On my machine, verification took about 9 minutes.
verifySingleConsensus = do
  putStr "VC #1 (reflexive).            "
  print =<< verify vc1                  
  putStr "VC #2 (transitive).           "
  print =<< verify vc2                  
  putStr "VC #3[Vo] (monotonic).        "
  print =<< verify vc3Vo                
  putStr "VC #3[Pr] (monotonic).        "
  print =<< verify vc3Pr                
  putStr "VC #3[Ac] (monotonic).        "
  print =<< verify vc3Ac              
  putStr "VC #4[Vo → Vo] (strong).      "
  print =<< verify   vc4VoVo            
  putStr "VC #4[Vo → Pr] (strong).      "
  print =<< verify   vc4VoPr            
  putStr "VC #4[Vo → Ac] (strong).      "
  print =<< verify   vc4VoAc            
  putStr "VC #4[Pr → Vo] (strong).      "
  print =<< verify   vc4PrVo            
  putStr "VC #4[Pr → Pr] (strong).      "
  print =<< verify   vc4PrPr            
  putStr "VC #4[Pr → Ac] (strong).      "
  print =<< verify   vc4PrAc            
  putStr "VC #4[Ac → Vo] (strong).      "
  print =<< verify   vc4AcVo            
  putStr "VC #4[Ac → Pr] (strong).      "
  print =<< verify   vc4AcPr            
  putStr "VC #4[Ac → Ac] (strong).      "
  print =<< verify   vc4AcAc
  putStr "VC #5[Vo ⇆ Vo] (commutable).  "
  print =<< verify   vc5VoVo
  putStr "VC #5[Vo ⇆ Pr] (commutable).  "
  print =<< verify   vc5VoPr
  putStr "VC #5[Vo ⇆ Ac] (commutable).  "
  print =<< verify   vc5VoAc
  putStr "VC #5[Pr ⇆ Pr] (commutable).  "
  print =<< verify   vc5PrPr
  putStr "VC #5[Pr ⇆ Ac] (commutable).  "
  print =<< verify   vc5PrAc
  putStr "VC #5[Ac ⇆ Ac] (commutable).  "
  print =<< verify vc5AcAc
