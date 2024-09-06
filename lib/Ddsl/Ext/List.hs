{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.List
  ( ListMd (listName)
  , ListWit
  , listWit
  , List (..)
  , prefixMatch
  , listLength
  , sublist
  , isEmptyList
  -- * Low-level
  , prefixMatchR
  , listLengthR
  , listTheory
  , mvwListLen
  , mvwListMatch
  ) where

import Ddsl
import Ddsl.Atom
import Ddsl.Ext.Map
import Ddsl.Ext.Nat
import Ddsl.Term

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.SBV
import GHC.Generics hiding (Rep)

data List i e = List [e] deriving (Show, Eq, Ord, Generic)

mvwL :: (ListMd i e) => ListWit i e -> Mvw (Rep (List i e)) SBool
mvwL _ = mvw

mvwMatch :: (ListMd i e) => ListWit i e -> Mvw (Rep (i, List i e, List i e)) SBool
mvwMatch _ = mvw

mvwListMatch :: (ListMd i e) => ListWit i e -> Mvw (Rep (i, List i e, List i e)) SBool
mvwListMatch = mvwMatch

mvwLen :: (ListMd i e) => ListWit i e -> Mvw (Rep (List i e)) (Rep i)
mvwLen _ = mvw

mvwListLen :: (ListMd i e) => ListWit i e -> Mvw (Rep (List i e)) (Rep i)
mvwListLen = mvwLen

class (SingleVal (Sv (List i e)), NatMd i, Avs e, Ava (List i e), SMTDefinable (Rep (List i e) -> SBool)) => ListMd i e where
  data ListWit i e
  listName :: ListWit i e -> String

  -- emptyListR :: ListWit i e -> MVFun (Rep (List i e)) SBool
  -- emptyListR w = mkMVFun (mvwL w) . ufList "emptyList" $ w

  prefixMatchR :: ListWit i e -> MVFun (Rep (i, List i e, List i e)) SBool
  prefixMatchR w = mkMVFun
    (mvwMatch w)
    (\(i,(l1,l2)) ->
       applyMV mvw (applyMV mvw (applyMV mvw (ufList "prefixMatch" w) i) l1) l2)

  listLengthR :: ListWit i e -> MVFun (Rep (List i e)) (Rep i)
  listLengthR w = mkMVFun (mvwLen w) . ufList "listLength" $ w

ufList :: (ListMd i e, SMTDefinable f) => String -> ListWit i e -> f
ufList name = uninterpret . (\s -> name ++ "__" ++ s) . listName

listWit :: (ListMd i e) => ListWit i e
listWit = undefined

-- emptyListTheory :: (ListMd i e) => ListWit i e -> Theory
-- emptyListTheory w = rule ("emptyList__" ++ listName w) $ do
--   let emptyList = applyMV (mvwL w) (emptyListR w)

--   -- Unique empty list
--   axiom $ \(l1,l2) -> (emptyList l1 .&& emptyList l2) .=> eqMV l1 l2

listTheory :: (ListMd i e) => ListWit i e -> Theory
listTheory w = rule' (zeroNatTheory (indexWit w) <> leNatTheory (indexWit w)) ("list__" ++ listName w) $ do
  let prefixMatch i l1 l2 = applyMV (mvwMatch w) (prefixMatchR w) (i,(l1,l2))
      listLength = applyMV (mvwLen w) (listLengthR w)
      le a1 a2 = applyMV (leMvw (indexWit w)) (leNatR (indexWit w)) (a1,a2)
      isZero = applyMV mvw (isZeroR (indexWit w))

  -- prefixMatch is reflexive up to listLength
  axiom $ \l -> prefixMatch (listLength l) l l

  -- -- prefixMatch symmetry
  -- axiom $ \(i,(l1,l2)) ->
  --   prefixMatch i l1 l2
  --   .<=> prefixMatch i l2 l1

  -- prefixMatch is transitive
  axiom $ \(i1,(i2,(l1,(l2,l3)))) ->
    (prefixMatch i1 l1 l2 .&& prefixMatch i2 l2 l3 .&& le i1 i2)
    .=> prefixMatch i1 l1 l3

  -- prefixMatch symmetry for equal lengths
  axiom $ \(l1,l2) ->
    (prefixMatch (listLength l1) l1 l2
     .&& (eqMV (listLength l2) (listLength l1)))
    .=> eqMV l1 l2

  -- prefixMatch on large index implies prefixMatch on small index
  axiom $ \(i1,(i2,(l1,l2))) ->
    (le i1 i2 .&& prefixMatch i2 l1 l2)
    .=> prefixMatch i1 l1 l2

  -- -- All lists with zero length are identical
  -- axiom $ \(l1,l2) ->
  --   (isZero (listLength l1)
  --    .&& isZero (listLength l2))
  --   .=> eqMV l1 l2

  -- All lists match up to zero
  axiom $ \(i,(l1,l2)) ->
    isZero i .=> prefixMatch i l1 l2

  -- prefix-match requires matched length
  axiom $ \(i,(l1,l2)) ->
    prefixMatch i l1 l2
    .=> (le i (listLength l1)
         .&& le i (listLength l2))

indexWit :: (ListMd i e) => ListWit i e -> NatWit i
indexWit _ = natWit

-- prefixMatchZeroTheory :: (ListMd i e) => ListWit i e -> Theory
-- prefixMatchZeroTheory w = rule' (zeroNatTheory (indexWit w)) ("prefixMatchZero__" ++ listName w) $ do
--   let prefixMatch i l1 l2 = applyMV (mvwMatch w) (prefixMatchR w) (i,(l1,l2))
--       isZero = applyMV mvw (isZeroR (indexWit w))

--   -- All lists match up to zero
--   axiom $ \(i,(l1,l2)) ->
--     isZero i .=> prefixMatch i l1 l2

-- prefixMatchLeTheory :: (ListMd i e) => ListWit i e -> Theory
-- prefixMatchLeTheory w = rule' (leNatTheory (indexWit w)) ("prefixMatchLe__" ++ listName w) $ do
--   let prefixMatch i l1 l2 = applyMV (mvwMatch w) (prefixMatchR w) (i,(l1,l2))
--       le a1 a2 = applyMV (leMvw (indexWit w)) (leNatR (indexWit w)) (a1,a2)

--   -- Prefix on large index implies prefix on small index
--   axiom $ \(i1,(i2,(l1,l2))) ->
--     (le i1 i2 .&& prefixMatch i2 l1 l2)
--     .=> prefixMatch i1 l1 l2

listLength'
  :: (Avs x, ListMd i e, NatMd i)
  => ListWit i e
  -> Alp x (List i e)
  -> Alp x i
listLength' w = eform $ atomFunTh
  (listTheory w)
  (listLengthR w)
  (\(List l) -> fromIntegral $ length l)

listLength
  :: (Avs x, ListMd i e, NatMd i)
  => Alp x (List i e)
  -> Alp x i
listLength = listLength' listWit

prefixMatch'
  :: (Avs x, ListMd i e)
  => ListWit i e
  -> Alp x i
  -> Alp x (List i e)
  -> Alp x (List i e)
  -> Alp x Bool
prefixMatch' w = eform3 $ atomFunTh
  (listTheory w)
  (prefixMatchR w)
  (error "prefixMatchR not runtime-implemented")

prefixMatch
  :: (Avs x, ListMd i e)
  => Alp x i
  -> Alp x (List i e)
  -> Alp x (List i e)
  -> Alp x Bool
prefixMatch = prefixMatch' listWit

sublist
  :: (Avs x, ListMd i e, NatMd i)
  => Alp x (List i e)
  -> Alp x (List i e)
  -> Alp x Bool
sublist = eform2 $
  atomWrapped
    (from2 $ \l1 l2 -> prefixMatch (listLength l1) l1 l2)
    (\(List l1, List l2) -> List.isPrefixOf l1 l2)

isEmptyList
  :: (Avs x, ListMd i e, NatMd i)
  => Alp x (List i e)
  -> Alp x Bool
isEmptyList = isZero . listLength

type LinkedList t i e
  = ((Bool, (t, i)), Map (t, i) (e, (Bool, (t, i))))

readLinkedList
  :: (Avs x, NatMd t, ListMd i e, MapMd (t,i) (e,(Bool,(t,i))))
  => Alp x (LinkedList t i e)
  -> Alp x (Bool, List i e)
readLinkedList = eform $ atomWrapped undefined f
  where
    f ((b,_),_) | not b = (True, List [])
    f ((_,k),m) = case Map.lookup k m of
      Just (e,next) ->
        let
          (r,List l') = f (next,m)
        in
          (r, List (e : l'))
      Nothing -> (False, List [])

emptyLinkedList
  :: (Avs x, NatMd t, ListMd i e, MapMd (t,i) (e,(Bool,(t,i))))
  => Alp x (LinkedList t i e)
emptyLinkedList = atomWrapped undefined f
  where
    f _ = ((False, undefined), Map.empty)
