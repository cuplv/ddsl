{-# LANGUAGE TemplateHaskell #-}

module SuperV where

import Prelude (print,putStr,putStrLn,(=<<),undefined,return,String,(++),map,concat,Maybe (..),mempty)

import Ddsl.Prelude

import Data.SBV (SBV)
import Language.Haskell.TH


-- Check that the monotonicity relation is reflexive.
vc1
  :: (Avs x, Avs u, Avs s)
  => (Alp x u -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x s -> Alp x s -> Alp x Bool)
  -> Alp x (u,s)
  -> Alp x Bool
vc1 integrity strongerOrEq args =
  from2' args $ \index s ->
  integrity index s ==> strongerOrEq index s s

-- Check that the monotonicity relation is transitive.
vc2
  :: (Avs x, Avs u, Avs s)
  => (Alp x u -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x s -> Alp x s -> Alp x Bool)
  -> Alp x (u,(s,s,s))
  -> Alp x Bool
vc2 integrity strongerOrEq args =
  from2' args $ \index states ->
  from3' states $ \s1 s2 s3 ->
  (integrity index s1
   && integrity index s2
   && integrity index s3
   && strongerOrEq index s1 s2
   && strongerOrEq index s2 s3)
  ==> strongerOrEq index s1 s3

-- Check that every valid Vote update satisfies the monotonicity
-- relation.  We will check the same thing for the Propose and Accept
-- updates.
vc3
  :: (Avs x, Avs u, Avs s, Avs i, Avs e)
  => (Alp x u -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x s -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x i -> Alp x e -> Alp x s -> Alp x Bool)
  -> (Alp x e -> Alp x s -> Alp x s)
  -> Alp x (u,(i,e,s))
  -> Alp x Bool
vc3 integrity strongerOrEq sup handle args =
  from2' args $ \uni ps ->
  from3' ps $ \origin update state1 ->
  let
    state2 = handle update state1
  in
    -- Assume that the update is valid.
    (integrity uni state1
     && sup uni origin update state1)
    -- Show that the change satisfies the monotonicity property.
    ==> (strongerOrEq uni state1 state2)

-- Check that every valid Vote update satisfies the monotonicity
-- relation.  We will check the same thing for the Propose and Accept
-- updates.
vc4
  :: (Avs x, Avs u, Avs s, Avs i, Avs e)
  => (Alp x u -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x i -> Alp x e -> Alp x s -> Alp x Bool)
  -> (Alp x e -> Alp x s -> Alp x s)
  -> Alp x (u,(i,e,s))
  -> Alp x Bool
vc4 integrity sup handle args =
  from2' args $ \uni ps ->
  from3' ps $ \origin update state1 ->
  let
    state2 = handle update state1
  in
    -- Assume that the update is valid.
    (integrity uni state1
     && sup uni origin update state1)
    -- Show that the change preserves integrity.
    ==> integrity uni state2

-- Check that every update is stable
vc5 -- :: Df ((Branch,Index), (NodeId, VoteE, NodeId, VoteE, State)) Bool
  :: (Avs x, Avs u, Avs s, Avs i, Avs e1, Avs e2)
  => (Alp x u -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x i -> Alp x e1 -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x i -> Alp x e2 -> Alp x s -> Alp x Bool)
  -> (Alp x e1 -> Alp x s -> Alp x s)
  -> (Alp x e2 -> Alp x s -> Alp x s)
  -> Alp x (u,(i,e1,i,e2,s))
  -> Alp x Bool
vc5 integrity sup1 sup2 handle1 handle2 args =
  from2' args $ \uni ps ->
  from5' ps $ \origin1 update1 origin2 update2 state1 ->
  let
    state2 = handle2 update2 state1
    pre1 = sup1 uni origin1 update1
    pre2 = sup2 uni origin2 update2
  in
    (integrity uni state1
     && pre1 state1
     && pre2 state1
     && (origin1 /= origin2))
    ==> pre1 state2

-- Check that every pair of valid updates commute.
vc6 -- :: Df ((Branch,Index), (NodeId, VoteE, NodeId, VoteE, State)) Bool
  :: (Avs x, Avs u, Avs s, Avs i, Avs e1, Avs e2)
  => (Alp x u -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x i -> Alp x e1 -> Alp x s -> Alp x Bool)
  -> (Alp x u -> Alp x i -> Alp x e2 -> Alp x s -> Alp x Bool)
  -> (Alp x e1 -> Alp x s -> Alp x s)
  -> (Alp x e2 -> Alp x s -> Alp x s)
  -> Alp x (u,(i,e1,i,e2,s))
  -> Alp x Bool
vc6 integrity sup1 sup2 handle1 handle2 x =
  from2' x $ \uni args ->
  from5' args $ \origin1 update1 origin2 update2 state ->
  let
    state1 = handle1 update1 state
    state12 = handle2 update2 state1
    state2 = handle2 update2 state
    state21 = handle1 update1 state2
  in
    -- Assume that the updates are valid,
    (integrity uni state
     -- && integrity uni state1
     -- && integrity uni state2
     -- && integrity uni state12
     -- && integrity uni state21
     && sup1 uni origin1 update1 state
     && sup2 uni origin2 update2 state
     -- and that they are concurrent.
     && (origin1 /= origin2))
    -- Show that the resulting states are identical.
    ==> (state12 == state21)


allOrderedPairs :: [a] -> [(a,a)]
allOrderedPairs [] = []
allOrderedPairs as = concat $ map p as
  where
    p a = map ((,) a) as

allUnorderedPairs :: [a] -> [(a,a)]
allUnorderedPairs [] = []
allUnorderedPairs (a:as) = map ((,) a) (a:as) ++ allUnorderedPairs as

myPrint :: (Show a) => a -> IO ()
myPrint a = putStrLn $ "    " ++ show a

mkVCs
  :: [(String,Name,Name)] -- ^ Handlers and SUPs
  -> [(String,Name)] -- ^ Actions
  -> Name -- ^ Integrity
  -> Name -- ^ Strength relation
  -> Q [Dec]
mkVCs updates acts integrity strongerOrEq = do
  c1 <- [d|checkVC1' :: SolverConfig -> IO ()
           checkVC1' conf = do
             putStrLn "VC #1 (strength is reflexive) ..."
             myPrint =<< verify' conf (vc1 $(varE integrity) $(varE strongerOrEq))
           checkVC1 :: IO ()
           checkVC1 = checkVC1' mempty
       |]
  c2 <- [d|checkVC2' :: SolverConfig -> IO ()
           checkVC2' conf = do
             putStrLn "VC #2 (strength is transitive) ..."
             myPrint =<< verify' conf (vc2 $(varE integrity) $(varE strongerOrEq))
           checkVC2 :: IO ()
           checkVC2 = checkVC2' mempty
        |]
  let
    mkVC3 (name, sup, handle) =
      [ noBindS [|putStrLn $ "VC #3 (" ++ $(litE $ stringL name) ++ " is strength-monotonic) ..."|]
      , noBindS [|myPrint =<< verify' conf (vc3 $(varE integrity) $(varE strongerOrEq) $(varE sup) $(varE handle))|]
      ]
  c3 <- [d|checkVC3' :: SolverConfig -> IO ()
           checkVC3' conf = $(doE (concat (map mkVC3 updates)))
           checkVC3 :: IO ()
           checkVC3 = checkVC3' mempty
        |]

  let
    mkVC4 (name, sup, handle) =
      [ noBindS [|putStrLn $ "VC #4 (" ++ $(litE $ stringL name) ++ " preserves local integrity) ..."|]
      , noBindS [|myPrint =<< verify' conf (vc4 $(varE integrity) $(varE sup) $(varE handle))|]
      ]
  c4 <- [d|checkVC4' :: SolverConfig -> IO ()
           checkVC4' conf = $(doE (concat (map mkVC4 updates)))
           checkVC4 :: IO ()
           checkVC4 = checkVC4' mempty
        |]

  let
    mkVC5 ((name1,sup1,handle1),(name2, sup2, handle2)) =
      [ noBindS [|putStrLn $ "VC #5 (" ++ $(litE $ stringL name1) ++ " is stable over " ++ $(litE $ stringL name2) ++ ") ..."|]
      , noBindS [|myPrint =<< verify' conf (vc5 $(varE integrity) $(varE sup1) $(varE sup2) $(varE handle1) $(varE handle2))|]
      ]
  c5 <- [d|checkVC5' :: SolverConfig -> IO ()
           checkVC5' conf = $(doE (concat (map mkVC5 $ allOrderedPairs updates)))
           checkVC5 :: IO ()
           checkVC5 = checkVC5' mempty
        |]

  let
    mkVC6 ((name1,sup1,handle1),(name2, sup2, handle2)) =
      [ noBindS [|putStrLn $ "VC #6 (" ++ $(litE $ stringL name1) ++ " and " ++ $(litE $ stringL name2) ++ " commute) ..."|]
      , noBindS [|myPrint =<< verify' conf (vc6 $(varE integrity) $(varE sup1) $(varE sup2) $(varE handle1) $(varE handle2))|]
      ]
  c6 <- [d|checkVC6' :: SolverConfig -> IO ()
           checkVC6' conf = $(doE (concat (map mkVC6 $ allUnorderedPairs updates)))
           checkVC6 :: IO ()
           checkVC6 = checkVC6' mempty
        |]

  cAll <- [d|checkAllVCs' :: SolverConfig -> IO ()
             checkAllVCs' conf = do
               checkVC1' conf
               checkVC2' conf
               checkVC3' conf
               checkVC4' conf
               checkVC5' conf
               checkVC6' conf
             checkAllVCs :: IO ()
             checkAllVCs = checkAllVCs' mempty
          |]
  return $ concat [c1,c2,c3,c4,c5,c6,cAll]
