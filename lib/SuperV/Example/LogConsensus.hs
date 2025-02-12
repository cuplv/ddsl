-- The following GHC language extensions are used to create symbolic
-- representations of the types in this example.
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module SuperV.Example.LogConsensus where

import Data.Word (Word32)
import Data.Store
import Data.Store.TH (makeStore)
import Prelude (Num,String)

import SuperV

-----------
-- TYPES --
-----------

-- | A node identifier (which is just a 'Word32').
newtype NodeId = NodeId Word32 deriving (Show,Eq,Ord)
-- Declare an opaque symbolic representation for 'NodeId'.
mkDType "NodeId" ''NodeId
makeStore ''NodeId

-- | A branch (also just a 'Word32').
newtype Branch = Branch Word32
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Branch'.
mkNatMd "Branch" ''Branch
-- We'll reason about sets of branches, so we declare this as well.
mkSetMd "Branch" ''Branch
makeStore ''Branch

-- | An index (also just a 'Word32').
newtype Index = Index Word32
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Branch'.
mkNatMd "Index" ''Index
makeStore ''Index

-- | A set of nodes eligible to vote.
type Voters = Set NodeId
-- Declare a symbolic representation for sets of 'NodeID's.
mkSetMd "NodeId" ''NodeId

-- | A count for node sets, to determine quorums
newtype NCount = NCount Word32
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

-- | An entry in the log (just a 'String')
newtype Entry = Entry String
  deriving (Show,Eq,Ord)
mkDType "Entry" ''Entry
makeStore ''Entry

-- | A record of accepts that a node has seen. The 'Accum' structure
-- is a map with a limited interface.
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
-- 'deferExists', which considers sets of Defer objects.
mkSetMd "Defer" ''Defer

type AcceptRule = ((Branch, Index), NodeId)
mkSetMd "AcceptRuleSet" ''AcceptRule

-- Tree stuff

-- | A 'Log' is a list of 'Entry's, which uses 'Index' to identify
-- positions in the log.
type Log = List Index Entry
mkListMd "Log" ''Index ''Entry

-- | Tree for storing log proposals, which uses 'Branch' as branch
-- identifiers and 'Index' as position identifiers within each branch.
type Tree = KtTree Branch Index Entry
mkKtTreeMd "LogTree" ''Branch ''Index ''Entry

instance Store (KtKey Branch Index)

ktw :: KtTreeWit Branch Index Entry
ktw = ktWit

lengthKt :: (Avs x) => Alp x Key -> Alp x Index
lengthKt = lengthKt' ktw

-- | A Branch + Index in the tree
type Key = KtKey Branch Index

-- | The eligible voters/accepters, the voting quorum size, and the
-- accepting quorum size.
type QState = (Voters, NCount, NCount)

-- | The main application state
type NodeState = (QState, Votes, (Branch, Key, Tree), Accepts)

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
-- An action can can "fail", in which case it returns False along with
-- the update message (idiomatic Haskell code would return a Maybe
-- type).  Actions are verified to only successfully produce an update
-- when the local state satisfies that update's Stable Update
-- Precondition (SUP).

-- An action takes the local node's ID, state, and some arguments:
-- in this case, the branch and candidate to vote for.
voteAction :: (Avs x) => Alp x NodeId -> Alp x NodeState -> Alp x (Branch,NodeId) -> Alp x (Bool, VoteE)
voteAction self state args =
  -- Unpack the state tuple using from4', binding its vote-map field
  -- as "votes".  The DSL's special representation of values prevents
  -- the use of idiomatic Haskell pattern-matching deconstruction.
  from4' state $ \_ votes _ _ ->
  -- Unpack the arguments: the branch that a leader is being elected
  -- for, and the candidate that is being voted for.
  from2' args $ \branch cand -> 
  -- Return a two-tuple, consisting of...
  tup2
    -- Action is successful when the local node has not voted yet
    -- (according to its local state).
    (keyNull (tup2 (fstE args) self) votes)
    -- Vote update value, using local node ID as the voter ID
    (tup3 branch self cand)

-- The propose action takes a proposal branch and entry as args.
proposeAction :: (Avs x) => Alp x NodeId -> Alp x NodeState -> Alp x (Branch,Entry) -> Alp x (Bool, ProposeE)
proposeAction self state args =
  from4' state $ \ev votes tree _ ->
  from3' tree $ \_ key _ ->
  from2' args $ \branch entry ->
  tup2
    -- This succeeds when the local node is elected for the argument branch.
    (isElected branch self ev votes)
    -- The generated update appends the new entry in the first index
    -- that the local node considers empty, indicated by 'key'.
    (tup3 key branch entry)

-- The accept action takes no special arguments.
acceptAction :: (Avs x) => Alp x NodeId -> Alp x NodeState -> Alp x () -> Alp x (Bool,AcceptE)
acceptAction self state _ =
  from4' state $ \ev votes tree accepts ->
  from3' tree $ \branch key body ->

  tup2
    -- It requires that the local node has not yet voted for any branch
    -- greater than the current branch.  This expression checks that no
    -- member of the "votes" set satisfies the predicate defined by the
    -- the given lambda expression.
    (nonePassMap "acceptAction" (tup2 branch self) votes
      (\args k _ ->
       from2' args $ \myBranch myNid ->
       from2' k $ \voteBranch voter ->
       (myNid $== voter)
       $/\ (voteBranch $> myBranch)))

    -- The update records an accept for the highest-witnessed index in
    -- the current branch.
    (tup3 branch self (lengthKt key))


--------------
-- HANDLERS --
--------------

-- | The handler for Vote updates
handleVote :: (Avs x) => Alp x VoteE -> Alp x NodeState -> Alp x NodeState
handleVote effect state =
  from3' effect $ \branch voter cand ->
  -- Modify the Votes field ...
  tup4m2 state $
    -- ... by inserting the new vote.
    insertMap (tup2 branch voter) cand

-- | The handler for Propose updates
handlePropose :: (Avs x) => Alp x ProposeE -> Alp x NodeState -> Alp x NodeState
handlePropose effect state =
  from3' effect $ \newKey newBranch entry ->
  from4' state $ \ev votes tree accepts ->
  from3' tree $ \oldBranch oldKey treeBody ->
  -- Create the new tree by appending the new entry at the given
  -- branch and index.
  let newTree = appendKt (tup2 newBranch entry) (tup2 newKey treeBody)
  -- Return a state containing the new tree.  If the given branch
  -- meets or exceeds the existing highest-branch, the head/key of the
  -- tree is updated to point to the new entry---otherwise, the
  -- head/key remains unchanged.
  in ite (newBranch >= oldBranch)
       (tup4 ev votes (tup3 newBranch (fstE newTree) (sndE newTree)) accepts)
       (tup4 ev votes (tup3 oldBranch oldKey (sndE newTree)) accepts)

-- | The handler for Accept updates
handleAccept :: (Avs x) => Alp x AcceptE -> Alp x NodeState -> Alp x NodeState
handleAccept effect state =
  from3' effect $ \branch accepter index ->
  tup4m4 state $
    -- Increase the accepted index for the accepter and branch to the
    -- given value (or leave it unchanged if it was already higher).
    advance (tup2 branch accepter) index

isElected :: (Avs x) => Alp x Branch -> Alp x NodeId -> Alp x (Voters, NCount, NCount) -> Alp x Votes -> Alp x Bool
isElected term cand qstate allVotes =
  from3' qstate $ \allVoters voteQ _ ->
  -- Check that the number of nodes, which are both eligible and have
  -- voted for cand in term, satisfies the configured vote-quorum
  -- threshold.
  commonCard (selectFst term $ selectV cand allVotes) allVoters
  >= voteQ

-- Check if the given index has a quorum of accepts for the given
-- branch.
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

getBranch :: (Avs x) => Alp x NodeState -> Alp x Branch
getBranch s =
  from4' s $ \_ _ t _ ->
  from3' t $ \b _ _ ->
  b

getAccepts :: (Avs x) => Alp x NodeState -> Alp x Accepts
getAccepts s =
  from4' s $ \_ _ _ as ->
  as

getQState :: (Avs x) => Alp x NodeState -> Alp x QState
getQState s = from4' s $ \q _ _ _ -> q

-----------------------
-- VERIFICATION SPEC --
-----------------------

-- True if any committed log in the first state is also committed in
-- the second state.
strongerOrEq :: (Avs x) => Alp x (Branch,Index) -> Binrel x NodeState
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

-- An integrity invariant on node states.  Our verification conditions
-- will check that every update preserves this condition.
integrity :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeState -> Alp x Bool
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

focusRule :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeState -> Alp x Bool
focusRule uniVals state =
  from2' uniVals $ \uniBranch uniIndex ->
  from4' state $ \ev _ tree accepts ->
  from3' tree $ \_ key body ->
  ((lengthKt key < uniIndex)
  && notE (deferExists uniVals state))
  ==> ((filterSet "focusRule" (tup3 uniBranch uniIndex accepts) fullSet $
    \args accepter ->
    from3' args $ \uniBranch uniIndex accepts ->
    notE $ upTo (tup2 uniBranch accepter) uniIndex accepts)
    == fullSet)

-- The stable precondition for Vote updates
supVote :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeId -> Alp x VoteE -> Alp x NodeState -> Alp x Bool
supVote uniVals origin update state =
  from4' state $ \_ vs _ _ ->
  from3' update $ \branch voter _ ->
  -- Check that origin has not yet voted in this term,
  -- and that the origin is voting in its own name.
  keyNull (tup2 branch voter) vs && (origin == voter)

-- The stable precondition for Propose updates.  Note that this
-- precondition takes an arbitrary Branch argument, which is
-- universally quantified in the verification conditions.
supPropose :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeId -> Alp x ProposeE -> Alp x NodeState -> Alp x Bool
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
       ==> deferExists uniVals state)
    -- and also, if we are not changing the branch, then our key must
    -- match treeHead, because no-one else can modify our branch.
    && ((latestBranch == pBranch) ==> (treeHead == pKey))

    -- Check that the old and new logs are well-formed
    && checkKt originLog
    && checkKt newLog

-- Check that no accepts exist for non-existent entries.
acceptRule :: (Avs x) => Alp x NodeState -> Alp x Bool
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
deferExists :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeState -> Alp x Bool
deferExists uniVals state =
  from4' state $ \qstate votes _ accepts ->
  from3' qstate $ \ev voteQ _ ->
  notE $ nonePassSet "deferExists" (tup5 uniVals ev accepts votes voteQ) fullSet $
    \args e ->
    from5' args $ \ti roll accepts votes voteQ ->
    isDefer e ti roll accepts votes voteQ

isDefer :: (Avs x) => Alp x Defer -> Alp x (Branch,Index) -> Alp x Voters -> Alp x Accepts -> Alp x Votes -> Alp x NCount -> Alp x Bool
isDefer def uniVals ev accepts votes voteQ =
  (fstE def > fstE uniVals)
  && (commonCard (sndE def) ev >= voteQ)
  -- Check that every member of the defer object has indeed committed
  -- to not accept the given branch and index (by voting in a higher
  -- branch election).  This is a universal quantification over
  -- 'NodeIds', for the predicate defined by the lambda expression.
  && universal "defers"
        (tup4 def uniVals accepts votes)
        (\args r ->
         from4' args $ \def uniVals accepts votes ->
         member r (sndE def)
         ==> (notE (upTo (tup2 (fstE uniVals) r) (sndE uniVals) accepts)
              && notE (keyNullPart (tup2 (fstE def) r) votes)))

bypass :: (Avs x) => Alp x Index -> Alp x (Key,Tree) -> Alp x (Key,Tree) -> Alp x Bool
bypass i l1 l2 =
  iteE
    (lengthKt (fstE l1) > i)
    (notE $ prefixMatchKt i l1 l2)
    (notE $ sublistKt l1 l2)

supAccept :: (Avs x) => Alp x (Branch,Index) -> Alp x NodeId -> Alp x AcceptE -> Alp x NodeState -> Alp x Bool
supAccept uniVals origin effect state =
  from3' effect $ \aBranch accepter index ->
  from4' state $ \_ votes tree _ ->
  from3' tree $ \latestBranch key _ ->
  -- Check that all conditions in the list are true.
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

-- This Template Haskell command generates the verification conditions
-- needed to verify that concurrent updates commute, and that each
-- node is individually monotonic with respect to the strength
-- ordering.  Together, these two conditions ensure consensus safety
-- for the committed-log decision.
--
-- When this module is loaded in GHCI, the function 'checkAllVCs' will
-- query an SMT solver (CVC5) for each verification condition in
-- sequence, printing the results.
mkVCs
  -- Updates (name, SUP, handler, generating action)
  [("Vote", 'supVote, 'handleVote, 'voteAction)
  ,("Propose", 'supPropose, 'handlePropose, 'proposeAction)
  ,("Accept", 'supAccept, 'handleAccept, 'acceptAction)
  ]
  -- Local integrity condition
  'integrity
  -- Strength ordering, defining the safety goal
  'strongerOrEq
