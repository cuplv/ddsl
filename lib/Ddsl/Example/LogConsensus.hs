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
import SuperV

import Prelude (print,putStr,(=<<),Num,String,undefined)

import Data.SBV (SBV,mkUninterpretedSort)

-----------
-- TYPES --
-----------

-- | A node identifier (which is just an 'Int').
newtype NodeId = NodeId Int deriving (Show,Eq,Ord)
-- Declare an opaque symbolic representation for 'NodeId'.
mkDType "NodeId" ''NodeId

-- | A branch (also just an 'Int').
newtype Branch = Branch Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Branch'.
mkNatMd "Branch" ''Branch
-- We'll reason about sets of branchs, so we declare this as well.
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

-- | A count for node sets, to determine quorums
newtype NCount = NCount Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
mkNatMd "NCount" ''NCount
instance CardSetMd NCount NodeId

-- | A voting node in a particular branch
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

-- A 'Defer' is a witness that certain branches' values can no longer
-- be accepted.  It consists of a quorum-size 'Voters' set and a
-- 'Branch' that they have all voted in.  This means that the voters are
-- not allowed to make new accepts for any older branch, and so any
-- older branch that none have accepted can no longer gather a quorum of
-- accepters.
type Defer = (Branch, Voters)
-- This is required for the 'nonePassSet' quantification in
-- 'rejecterExists'.
mkSetMd "Defer" ''Defer

type AcceptRule = ((Branch, Index), NodeId)
mkSetMd "AcceptRuleSet" ''AcceptRule

-- Tree stuff 

type Log = List Index Entry
mkListMd "Log" ''Index ''Entry

-- | Tree for storing log proposals
type Tree = KtTree Branch Index Entry
mkKtTreeMd "LogTree" ''Branch ''Index ''Entry

ktw :: KtTreeWit Branch Index Entry
ktw = ktWit

lengthKt :: (Avs x) => Alp x Key -> Alp x Index
lengthKt = lengthKt' ktw

-- | A Branch + Index in the tree
type Key = KtKey Branch Index

-- | The eligible voters/accepters, the voting quorum size, and the
-- accepting quorum size.
type QState = (Voters, NCount, NCount)

-- | The main Ferry application state
type State = (QState, Votes, (Branch, Key, Tree), Accepts)

-- | The Vote effect type
type VoteE = (Branch,NodeId,NodeId)

-- | The Propose effect type
type ProposeE = (KtKey Branch Index, Branch, Entry)

-- | The Accept effect type
type AcceptE = (Branch, NodeId, Index)

-- We declare a single manual quantifier alternaton edge, from the
-- given tuple type to the 'NodeId' type.
--
-- Automatic quantifier alternation edges are created from Sets and
-- Maps to their elements.
--
-- Note that manually-declared quantifier alternation edges are NOT
-- checked for conflicts: this is not possible using Haskell's
-- typeclass system.  To avoid defining conflicting edges, declare all
-- edges in one place in your source file.
instance QE (Defer, (Branch, Index), Accepts, Votes) NodeId


-------------
-- ACTIONS --
-------------

-- These are called by application code to modify the state.
--
-- An action can can "fail", in which case it returns False
-- along with the update message (idiomatic Haskell code would return
-- a Maybe type).  Actions are verified to only successfully
-- produce an update when the local state satisfies that update's SUP.

-- An action takes the local node's ID, state, and some arguments:
-- in this case, the branch and candidate to vote for.
voteAction :: (Avs x) => Alp x NodeId -> Alp x State -> Alp x (Branch,NodeId) -> Alp x (Bool, VoteE)
voteAction self state args =
  from4' state $ \_ votes _ _ ->
  -- Action is successful when the local node has not voted yet
  -- (according to its local state).
  keyNull (tup2 (fstE args) self) votes
  -- Uses local node ID as the voter ID.
  &&& (tup3 (fstE args) self (sndE args))

-- The propose action takes a proposal branch and entry as args.
proposeAction :: (Avs x) => Alp x NodeId -> Alp x State -> Alp x (Branch,Entry) -> Alp x (Bool, ProposeE)
proposeAction self state args =
  from4' state $ \ev votes tree _ ->
  from3' tree $ \_ key body ->
  from2' args $ \branch entry ->

  -- This succeeds when the local node is elected for the argument branch.
  isElected branch self ev votes
  -- The generated update appends the new entry in the first index
  -- that the local node considers empty.
  &&& tup3 key branch entry

-- The accept generator takes no special arguments.
acceptAction :: (Avs x) => Alp x NodeId -> Alp x State -> Alp x () -> Alp x (Bool,AcceptE)
acceptAction self state _ =
  from4' state $ \ev votes tree accepts ->
  from3' tree $ \branch key body ->

  -- It requires that the local node has not yet voted for any branch
  -- greater than the current branch.
  nonePassMap "acceptAction" (tup2 branch self) votes
    (\args k _ ->
     from2' args $ \myBranch myNid ->
     from2' k $ \voteBranch voter ->
     (myNid $== voter)
     $/\ (voteBranch $> myBranch))

  -- The update records an accept for the highest-witnessed index in
  -- the current branch.
  &&& tup3 branch self (lengthKt key)


--------------
-- HANDLERS --
--------------

-- | The handler for Vote updates
handleVote :: (Avs x) => Alp x VoteE -> Alp x State -> Alp x State
handleVote effect state =
  from3' effect $ \branch voter cand ->
  -- Modify the Votes field ...
  tup4m2 state $
    -- ... by inserting the new vote.
    insertMap (tup2 branch voter) cand

-- | The handler for Propose updates
handlePropose :: (Avs x) => Alp x ProposeE -> Alp x State -> Alp x State
handlePropose effect state =
  from3' effect $ \newKey newBranch entry ->
  from4' state $ \ev votes tree accepts ->
  from3' tree $ \oldBranch oldKey treeBody ->
  let newLog = appendKt (tup2 newBranch entry) (tup2 newKey treeBody)
  in ite (newBranch >= oldBranch)
       (tup4 ev votes (tup3 newBranch (fstE newLog) (sndE newLog)) accepts)
       (tup4 ev votes (tup3 oldBranch oldKey (sndE newLog)) accepts)

-- | The handler for Accept updates
handleAccept :: (Avs x) => Alp x AcceptE -> Alp x State -> Alp x State
handleAccept effect state =
  from3' effect $ \branch accepter index ->
  tup4m4 state $
    advance (tup2 branch accepter) index

isElected :: (Avs x) => Alp x Branch -> Alp x NodeId -> Alp x (Voters, NCount, NCount) -> Alp x Votes -> Alp x Bool
isElected term cand qstate allVotes =
  from3' qstate $ \allVoters voteQ _ ->
  -- Check that the number of nodes are both eligible and have voted
  -- for cand in term satisfies the configured vote-quorum.
  commonCard (selectFst term $ selectV cand allVotes) allVoters
  >= voteQ

isCommittedB :: (Avs x) => Alp x Branch -> Alp x Index -> Alp x Accepts -> Alp x (Voters, NCount, NCount) -> Alp x Bool
isCommittedB branch index accepts qstate =
  from3' qstate $ \ev _ acceptQ -> 
  let accepters = filterSet "isCommittedB" (tup3 branch index accepts) ev $
        \args voter ->
        from3' args $ \branch index accepts ->
        upTo (tup2 branch voter) index accepts
     -- Check that the number of voters common to the accepter-set and
     -- eligible-set meets (their intersection) meets or exceeds the
     -- configured accept-quroum size.
  in commonCard accepters ev >= acceptQ

-----------------------
-- VERIFICATION SPEC --
-----------------------

strongerOrEq :: (Avs x) => Alp x (Branch,Index) -> Binrel x State
strongerOrEq uniVals state1 state2 =
  from2' uniVals $ \uniBranch uniIndex ->
  from4' state1 $ \ev1 _ tree1 accepts1 ->
  from3' tree1 $ \_ key1 body1 ->
  from4' state2 $ \ev2 _ tree2 accepts2 ->
  from3' tree2 $ \_ key2 body2 ->
  isCommittedB uniBranch uniIndex accepts1 ev1
  ==> (isCommittedB uniBranch uniIndex accepts2 ev2
       && prefixMatchKt uniIndex (tup2 key1 body1) (tup2 key2 body2)
      )

----------------------------
-- VERIFICATION ARTIFACTS --
----------------------------

-- An integrity invariant on node states, which every SUP assumes
integrity :: (Avs x) => Alp x (Branch,Index) -> Alp x State -> Alp x Bool
integrity uniVals state =
  from2' uniVals $ \uniBranch uniIndex ->
  from4' state $ \qstate _ tree accepts ->
  from3' tree $ \_ key body ->
  -- Accepts do not exist for entries that do not exist
  acceptRule state && focusRule uniVals state
  -- Rules for flexible quorums
  && quorumRule qstate
  -- The log is well-formed
  && checkKt (tup2 key body)

quorumRule :: (Avs x) => Alp x (Voters, NCount, NCount) -> Alp x Bool
quorumRule qstate = from3' qstate $ \ev voteQ acceptQ ->
  let clusterSize = card ev
     -- clusterSize <= (voteQ + acceptQ)
  in ltSum clusterSize voteQ acceptQ
     -- clusterSize <= (acceptQ + acceptQ)
     && ltSum clusterSize acceptQ acceptQ
     && (voteQ > acceptQ)
     && (acceptQ > zero)

focusRule :: (Avs x) => Alp x (Branch,Index) -> Alp x State -> Alp x Bool
focusRule uniVals state =
  from2' uniVals $ \uniBranch uniIndex ->
  from4' state $ \ev _ tree accepts ->
  from3' tree $ \_ key body ->
  ((lengthKt key < uniIndex)
  && notE (rejecterExists uniVals state))
  ==> ((filterSet "focusRule" (tup3 uniBranch uniIndex accepts) fullSet $
    \args accepter ->
    from3' args $ \uniBranch uniIndex accepts ->
    notE $ upTo (tup2 uniBranch accepter) uniIndex accepts)
    == fullSet)

-- The precondition for Vote updates
supVote :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeId -> Alp x VoteE -> Alp x State -> Alp x Bool
supVote uniVals origin update state =
  from4' state $ \_ vs _ _ ->
  from3' update $ \branch voter _ ->
  -- Check that origin has not yet voted in this term,
  -- and that the origin is voting in its own name.
  keyNull (tup2 branch voter) vs && (origin == voter)

-- The precondition for Propose updates.  Note that this precondition
-- takes an arbitrary Branch argument, which is universally quantified
-- in the verification conditions.
supPropose :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeId -> Alp x ProposeE -> Alp x State -> Alp x Bool
supPropose uniVals origin update state =
  from2' uniVals $ \uniBranch uniIndex ->
  from4' state $ \qstate vs tree as ->
  from3' tree $ \latestBranch treeHead treeBody ->
  from3' update $ \pKey pBranch pEntry ->
  let
    originLog = tup2 pKey treeBody
    newLog = appendKt (tup2 pBranch pEntry) originLog
  in
    -- Check that origin is elected for the proposal branch,
    isElected pBranch origin qstate vs
    -- and that no invalid accepts exist,
    && acceptRule state
    -- and that, if we are bypassing, then the entries we are
    -- bypassing must be deferred,
    && (((pBranch > latestBranch) && (latestBranch >= uniBranch)
        && bypass uniIndex (tup2 treeHead treeBody) newLog)
       ==> rejecterExists uniVals state)
    -- and also, if we are not changing the branch, then our key must
    -- match treeHead, because no-one else can modify our branch.
    && ((latestBranch == pBranch) ==> (treeHead == pKey))

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

-- Check that a Defer witness exists for the given Branch.
rejecterExists :: (Avs x) => Alp x (Branch,Index) -> Alp x State -> Alp x Bool
rejecterExists uniVals state =
  from4' state $ \qstate votes _ accepts ->
  from3' qstate $ \ev voteQ _ ->
  notE $ nonePassSet "rejecterExists" (tup5 uniVals ev accepts votes voteQ) fullSet $
    \args e ->
    from5' args $ \ti roll accepts votes voteQ ->
    isDefer e ti roll accepts votes voteQ

isDefer :: (Avs x) => Alp x Defer -> Alp x (Branch,Index) -> Alp x Voters -> Alp x Accepts -> Alp x Votes -> Alp x NCount -> Alp x Bool
isDefer rej uniVals ev accepts votes voteQ =
  (fstE rej > fstE uniVals)
  && (commonCard (sndE rej) ev >= voteQ)
  && universal "rejects"
        (tup4 rej uniVals accepts votes)
        (\args r ->
         from4' args $ \rej uniVals accepts votes ->
         member r (sndE rej)
         ==> (notE (upTo (tup2 (fstE uniVals) r) (sndE uniVals) accepts)
              && notE (keyNullPart (tup2 (fstE rej) r) votes)))

bypass :: (Avs x) => Alp x Index -> Alp x (Key,Tree) -> Alp x (Key,Tree) -> Alp x Bool
bypass i l1 l2 =
  iteE
    (lengthKt (fstE l1) > i)
    (notE $ prefixMatchKt i l1 l2)
    (notE $ sublistKt l1 l2)

supAccept :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeId -> Alp x AcceptE -> Alp x State -> Alp x Bool
supAccept uniVals origin effect state =
  from3' effect $ \aBranch accepter index ->
  from4' state $ \_ votes tree _ ->
  from3' tree $ \latestBranch key _ ->
  andAllA
    [ accepter == origin
    , ((index <= lengthKt key) && (aBranch <= latestBranch))
      || (aBranch < latestBranch)
    , nonePassMap "acceptSup" (tup2 aBranch origin) votes $
        \args k _ ->
        from2' args $ \aBranch origin ->
        from2' k $ \vBranch voter ->
        (voter == origin) && (vBranch > aBranch)
    ]

mkVCs
  -- Updates
  [("Vote", 'supVote, 'handleVote, 'voteAction)
  ,("Propose", 'supPropose, 'handlePropose, 'proposeAction)
  ,("Accept", 'supAccept, 'handleAccept, 'acceptAction)
  ]
  -- Local integrity condition
  'integrity
  -- Decision strength relation
  'strongerOrEq
