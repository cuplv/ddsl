module Ddsl.Example.LogConsensus.VC where

import Prelude (print,putStr,(=<<))

import Ddsl.Prelude
import Ddsl.Example.LogConsensus

-----------------------------
-- VERIFICATION CONDITIONS --
-----------------------------

-- Check that the monotonicity relation is reflexive.
vc1 :: Df ((Branch,Index), State) Bool
vc1 args =
  from2' args $ \index s ->
  integrity index s ==> strongerOrEq index s s

-- Check that the monotonicity relation is transitive.
vc2 :: Df ((Branch,Index), (State, State, State)) Bool
vc2 args =
  from2' args $ \index states ->
  from3' states $ \s1 s2 s3 ->
  (strongerOrEq index s1 s2
   && strongerOrEq index s2 s3)
  ==> strongerOrEq index s1 s3

-- Check that every valid Vote update satisfies the monotonicity
-- relation.  We will check the same thing for the Propose and Accept
-- updates.
vc3Vo :: Df ((Branch,Index), (NodeId, VoteE, State)) Bool
vc3Vo args =
  from2' args $ \uni ps ->
  from3' ps $ \origin update state1 ->
  let
    state2 = handleVote update state1
  in
    -- Assume that the update is valid.
    (supVote origin update state1 && integrity uni state1)
    -- Show that the change satisfies the monotonicity property.
    ==> (strongerOrEq uni state1 state2 && integrity uni state2)

vc3Pr :: Df ((Branch,Index), (NodeId, ProposeE, State)) Bool
vc3Pr args =
  from2' args $ \uni ps ->
  from3' ps $ \origin update state1 ->
  let
    state2 = handlePropose update state1
  in
    (supPropose uni origin update state1 && integrity uni state1)
    ==> (strongerOrEq uni state1 state2
         -- && integrity uni state2
        )

vc3Ac :: Df ((Branch,Index), (NodeId, AcceptE, State)) Bool
vc3Ac args =
  from2' args $ \uni ps ->
  from2' uni $ \branch _ ->
  from3' ps $ \origin update state1 ->
  let
    state2 = handleAccept update state1
  in
    (supAccept origin update state1 && integrity uni state1)
    ==> (strongerOrEq uni state1 state2 && integrity uni state2)

-- Check that every update's precondition is "strong": that it is
-- preserved by any other update that is valid
-- (precondition-satisfying) and concurrent (distinct origin node).
--
-- We must perform this check for every combination of possible
-- updates, in every order, so there are 9 total instances of this
-- condition.
vc4VoVo :: Df ((Branch,Index), (NodeId, VoteE, NodeId, VoteE, State)) Bool
vc4VoVo args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handleVote update2 state1
    pre1 = supVote origin1 update1
  in
    (supVote origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4PrVo :: Df ((Branch,Index), (NodeId, VoteE, NodeId, ProposeE, State)) Bool
vc4PrVo args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handlePropose update2 state1
    pre1 = supVote origin1 update1
  in
    (supPropose uni origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4AcVo :: Df ((Branch,Index), (NodeId, VoteE, NodeId, AcceptE, State)) Bool
vc4AcVo args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handleAccept update2 state1
    pre1 = supVote origin1 update1
  in
    (supAccept origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4VoPr :: Df ((Branch,Index), (NodeId, ProposeE, NodeId, VoteE, State)) Bool
vc4VoPr args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handleVote update2 state1
    pre1 = supPropose uni origin1 update1
  in
    (supVote origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4PrPr :: Df ((Branch,Index), (NodeId, ProposeE, NodeId, ProposeE, State)) Bool
vc4PrPr args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handlePropose update2 state1
    pre1 = supPropose uni origin1 update1
  in
    (supPropose uni origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4AcPr :: Df ((Branch,Index), (NodeId, ProposeE, NodeId, AcceptE, State)) Bool
vc4AcPr args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handleAccept update2 state1
    pre1 = supPropose uni origin1 update1
  in
    (supAccept origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4VoAc :: Df ((Branch,Index), (NodeId, AcceptE, NodeId, VoteE, State)) Bool
vc4VoAc args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handleVote update2 state1
    pre1 = supAccept origin1 update1
  in
    (supVote origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4PrAc :: Df ((Branch,Index), (NodeId, AcceptE, NodeId, ProposeE, State)) Bool
vc4PrAc args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handlePropose update2 state1
    pre1 = supAccept origin1 update1
  in
    (supPropose uni origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

vc4AcAc :: Df ((Branch,Index), (NodeId, AcceptE, NodeId, AcceptE, State)) Bool
vc4AcAc args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handleAccept update2 state1
    pre1 = supAccept origin1 update1
  in
    (supAccept origin2 update2 state1
    && integrity uni state1
    && (origin1 /= origin2))
    ==> (pre1 state1 ==> pre1 state2)

-- Check that every pair of valid updates commute.
--
-- We must check this for every combinataion of updates, but it is
-- un-ordered, so there are 6 total instances of this condition.
vc5VoVo :: Df ((Branch,Index), (NodeId, VoteE, NodeId, VoteE, State)) Bool
vc5VoVo x =
  from2' x $ \uni args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      handleVote update2
        (handleVote update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      handleVote update1
        (handleVote update2 state)
  in
    -- Assume that the updates are valid,
    (supVote origin1 update1 state
    && supVote origin2 update2 state
    && integrity uni state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5VoPr :: Df ((Branch,Index), (NodeId, VoteE, NodeId, ProposeE, State)) Bool
vc5VoPr x =
  from2' x $ \uni args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      handlePropose update2
        (handleVote update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      handleVote update1
        (handlePropose update2 state)
  in
    -- Assume that the updates are valid,
    (supVote origin1 update1 state
    && supPropose uni origin2 update2 state
    && integrity uni state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5VoAc :: Df ((Branch,Index), (NodeId, VoteE, NodeId, AcceptE, State)) Bool
vc5VoAc x =
  from2' x $ \uni args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      handleAccept update2
        (handleVote update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      handleVote update1
        (handleAccept update2 state)
  in
    -- Assume that the updates are valid,
    (supVote origin1 update1 state
    && supAccept origin2 update2 state
    && integrity uni state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5PrPr :: Df ((Branch,Index), (NodeId, ProposeE, NodeId, ProposeE, State)) Bool
vc5PrPr x =
  from2' x $ \uni args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      handlePropose update2
        (handlePropose update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      handlePropose update1
        (handlePropose update2 state)
  in
    -- Assume that the updates are valid,
    (supPropose uni origin1 update1 state
    && supPropose uni origin2 update2 state
    && integrity uni state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5PrAc :: Df ((Branch,Index), (NodeId, ProposeE, NodeId, AcceptE, State)) Bool
vc5PrAc x =
  from2' x $ \uni args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      handleAccept update2
        (handlePropose update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      handlePropose update1
        (handleAccept update2 state)
  in
    -- Assume that the updates are valid,
    (supPropose uni origin1 update1 state
    && supAccept origin2 update2 state
    && integrity uni state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

vc5AcAc :: Df ((Branch,Index), (NodeId, AcceptE, NodeId, AcceptE, State)) Bool
vc5AcAc x =
  from2' x $ \uni args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    -- The result of applying update1 and then update2.
    state12 =
      handleAccept update2
        (handleAccept update1 state)
    -- The result of applying update2 and then update1.
    state21 =
      handleAccept update1
        (handleAccept update2 state)
  in
    -- Assume that the updates are valid,
    (supAccept origin1 update1 state
    && supAccept origin2 update2 state
    && integrity uni state
    -- and that they are concurrent.
    && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)

-- On my machine, verification took about 9 minutes.
verifyLogConsensus = do
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
