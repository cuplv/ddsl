{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Example.LogConsensus where

import Ddsl.Prelude

import Prelude (print,putStr,(=<<),Num,String,undefined)

import Data.SBV (SBV,mkUninterpretedSort)

-----------
-- TYPES --
-----------

-- | A node identifier (which is just an 'Int').
newtype NodeId = NodeId Int deriving (Show,Eq,Ord)
-- Declare an opaque symbolic representation for 'NodeId'.
mkDType "NodeId" ''NodeId

-- | A term (also just an 'Int').
newtype Branch = Branch Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Branch'.
mkNatMd "Branch" ''Branch
-- We'll reason about sets of terms, so we declare this as well.
mkSetMd "Branch" ''Branch

-- | An index (also just an 'Int').
newtype Index = Index Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Branch'.
mkNatMd "Index" ''Index

-- | A set of nodes eligible to vote.
type Voters = Set NodeId
-- Declare a symbolic representation for sets of 'NodeID's.
mkSetMd "NodeId" ''NodeId

-- | A voting node in a particular term
type VoterId = (Branch,NodeId)
-- | A record of votes
type Votes = Map VoterId NodeId
mkSetMd "Branch_NodeId" ''VoterId
-- Declare a symbolic representation for the Votes map.
mkMapMd "Branch_NodeId_NodeId" ''VoterId ''NodeId

-- | An entry in the log (actually just a 'String')
newtype Entry = Entry String
  deriving (Show,Eq,Ord)
mkDType "Entry" ''Entry

-- | A record of accepts
type Accepts = Accum (Branch,NodeId) Index
mkAccumMd "Branch_NodeId_Index" ''VoterId ''Index

-- A 'Rejecter' is a witness that certain terms' values can no longer
-- be accepted.  It consists of a quorum-size 'Voters' set and a
-- 'Term' that they have all voted in.  This means that the voters are
-- not allowed to make new accepts for any older term, and so any
-- older term that none have accepted can no longer gather a quorum of
-- accepters.
type Rejecter = (Branch, Voters)
-- This is required for the 'nonePassSet' quantification in
-- 'rejecterExists'.
mkSetMd "Rejecter" ''Rejecter

type AcceptRule = ((Branch, Index), NodeId)
mkSetMd "AcceptRuleSet" ''AcceptRule

-- Tree stuff 

data Log_S
mkUninterpretedSort ''Log_S
data LK_S
mkUninterpretedSort ''LK_S
data LT_S
mkUninterpretedSort ''LT_S

instance SingleVal Log_S

type Log = List Index Entry

instance Avs Log where
  type Rep Log = SBV Log_S

instance Ava Log where
  type Sv Log = Log_S

instance ListMd Index Entry where
  data ListWit Index Entry
  listName _ = "Index__Entry"

instance SingleVal LK_S

type LK = KtKey Branch Index

instance Avs LK where
  type Rep LK = SBV LK_S

instance Ava LK where
  type Sv LK = LK_S

instance SingleVal LT_S

type LT = KtTree Branch Index Entry

instance Avs LT where
  type Rep LT = SBV LT_S

instance Ava LT where
  type Sv LT = LT_S

ktw :: KtTreeWit Branch Index Entry
ktw = ktWit

lengthKt :: (Avs x) => Alp x Key -> Alp x Index
lengthKt = lengthKt' ktw

type Tree = KtTree Branch Index Entry
instance KtTreeMd Branch Index Entry where
  data KtTreeWit Branch Index Entry
  ktTreeName _ = "KtLog"

type Key = KtKey Branch Index

type State = (Voters, Votes, (Branch, Key, Tree), Accepts)

type VoteE = (Branch,NodeId,NodeId)

type ProposeE = (KtKey Branch Index, Branch, Entry)

type AcceptE = (Branch, NodeId, Index)

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
instance QE (Rejecter, (Branch, Index), Accepts, Votes) NodeId

-------------
-- ACTIONS --
-------------

startCampaign :: (Avs x) => Alp x () -> Alp x NodeId -> Alp x State -> Alp x ((Bool,VoteE),())
startCampaign _ self state =
  -- Get the next branch higher than seen in any existing votes
  let myBranch = undefined
  in tup2 (tup2 trueE (tup3 myBranch self self)) unitE

reactToVote :: (Avs x) => Alp x () -> Alp x NodeId -> Alp x State -> Alp x ((Bool,VoteE),())
reactToVote _ self state =  
  let -- Get the highest branch that has been voted for,
      -- and an arbitrary candidate that has received that vote.
      highestVote = undefined
      -- Check if we have voted in it yet
      iVoted = undefined
  in ite iVoted
       -- If true, don't send the vote update
       undefined
       -- Else, send the vote update
       undefined

------------------
-- VERIFICATION --
------------------

-- The precondition for Vote updates
votePre :: (Avs x) => Alp x NodeId -> Alp x VoteE -> Alp x State -> Alp x Bool
votePre origin update state =
  from4' state $ \_ vs _ _ ->
  from3' update $ \branch voter _ ->
  -- Check that origin has not yet voted in this term,
  -- and that the origin is voting in its own name.
  keyNull (tup2 branch voter) vs && (origin == voter)

-- The precondition for Propose updates.  Note that this precondition
-- takes an arbitrary Branch argument, which is universally quantified
-- in the verification conditions.
proposePre :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeId -> Alp x ProposeE -> Alp x State -> Alp x Bool
proposePre uniVals origin update state =
  from2' uniVals $ \uniBranch uniIndex ->
  from4' state $ \ev vs tree as ->
  from3' tree $ \latestBranch treeHead treeBody ->
  from3' update $ \pKey pBranch pEntry ->
  let
    originLog = tup2 pKey treeBody
    newLog = appendKt (tup2 pBranch pEntry) originLog
  in
    -- Check that origin is elected for the proposal term,
    isElected pBranch origin (tup2 ev vs)
    -- and that no invalid accepts exist,
    && acceptRule state
    -- and that, if the proposal term exceeds the current term, then
    -- either ...
    && (((pBranch > latestBranch) && (latestBranch >= uniBranch)
        && dchange uniIndex (tup2 treeHead treeBody) newLog)
       ==> rejecterExists uniVals state)

    -- Do we need these?
    && checkKt originLog
    && checkKt newLog

acceptRule :: (Avs x) => Alp x State -> Alp x Bool
acceptRule state =
  from4' state $ \_ _ tree accepts ->
  from3' tree $ \latestBranch key _ ->
  allPassSet "invarAcceptRules"
     (from2 $ \args e ->
      from2' e $ \ti r ->
      from2' ti $ \t i ->
      from3' args $ \st si sa ->
      upTo (t &&& r) i sa
      $=> (((st $> t)
            $\/ ((st $== t) $/\ (si $>= i))
            $\/ ((st $< t) $/\ (isZero i)))
          )
     )
     (tup3 latestBranch (lengthKt key) accepts)
     fullSet

isElected :: (Avs x) => Alp x Branch -> Alp x NodeId -> Alp x (Voters, Votes) -> Alp x Bool
isElected term cand state =
  from2' state $ \allVoters allVotes ->
  -- Check that the set of nodes that have voted for cand in term
  -- is a quorum of the eligible voters.
  selectFst term (selectV cand allVotes) `quorum` allVoters

-- Check that a Rejecter witness exists for the given Branch.
rejecterExists :: (Avs x) => Alp x (Branch,Index) -> Alp x State -> Alp x Bool
rejecterExists uniVals state =
  from4' state $ \ev votes _ accepts ->
  nonePassSet "rejecterExists" (tup4 uniVals ev accepts votes) fullSet $
    \args e ->
    from4' args $ \ti roll accepts votes ->
    isRejecter e ti roll accepts votes

isRejecter :: (Avs x) => Alp x Rejecter -> Alp x (Branch,Index) -> Alp x Voters -> Alp x Accepts -> Alp x Votes -> Alp x Bool
isRejecter rej uniVals ev accepts votes =
  (fstE rej $> fstE uniVals)
  && quorum (sndE rej) ev
  && universal "rejects"
        (tup4 rej uniVals accepts votes)
        (\args r ->
         from4' args $ \rej uniVals accepts votes ->
         member r (sndE rej)
         $=> (notE (upTo (fstE uniVals &&& r) (sndE uniVals) accepts)
              $/\ notE (keyNullPart (fstE rej &&& r) votes)))

  -- from2' rj $ \rBranch rVoters ->
  -- -- rj is a rejecter for t only if...
  -- --
  -- -- rj's term is greater than t,
  -- (rBranch > t)
  -- -- and rj's voters are a quorum,
  -- && quorum rVoters ev
  -- -- and each of rj's voters meet the following conditions:
  -- --
  -- -- (this function universally quantifies over all 'NodeId's in the
  -- -- context of the explicit arguments @(tup4 rj t vs as)@, and so we
  -- -- had to define the 'QE' quanfier edge at the top of the file)
  -- && (universal "isRejecter" (tup4 rj t vs as) $
  --   \args voter ->
  --   from4' args $ \rj t vs as ->
  --   from2' rj $ \rBranch rVoters ->
  --   member voter rVoters ==>
  --     -- each voter has not accepted term t,
  --     (not (member (tup2 t voter) as)
  --     -- and each voter has voted in rj's term.
  --     && not (keyNullPart (tup2 rBranch voter) vs)))

dchange :: (Avs x) => Alp x Index -> Alp x (Key,Tree) -> Alp x (Key,Tree) -> Alp x Bool
dchange i l1 l2 =
  iteE
    (lengthKt (fstE l1) > i)
    (notE $ prefixMatchKt i l1 l2)
    (notE $ sublistKt l1 l2)
