{-# LANGUAGE FlexibleContexts #-}

module Ddsl.Ext.Set
  ( SetMd (elementName)
  , mkSetMd
  , SetWit
  , setWit
  , Set
  , emptySet
  , isEmptySet
  , fullSet
  , isFullSet
  , member
  , subset
  , quorum
  , insertSet
  , selectFst
  , flatSelectFst
  , selectSnd
  -- , intersection
  -- , disjoint
  -- , select1
  -- , select2
  , SetFilter
  , mkSetFilter
  -- , annotateSetFilter
  , filterSet'
  , filterSet
  , filterSetE
  , allPassSet
  , nonePassSet
  , somePassSet
  , nonePassSet'
  , somePassSet'
  -- * Low-level
  , emptySetR
  -- , fstSet
  -- , sndSet
  , memberTheory
  , emptySetTheory
  , fullSetTheory
  , subsetTheory
  , quorumTheory
  , setTheory
  , subsetMvw
  , subsetR
  ) where

import Ddsl
import Ddsl.Atom (atomWrapped)
import Ddsl.Ext.Set.Class
import Ddsl.Ext.Set.Filter
import Ddsl.Ext.Set.TH

import qualified Data.Set as Set

import Data.SBV (SMTDefinable,SBool)

selectFst
  :: (Avs x, Avs e1, SetMd (e1,e2), SetMd e2, SMTDefinable (MVFun (Rep e1) (Rep (Set (e1,e2)) -> Rep (Set e2) -> Rep (Set e2) -> SBool)), Ord e1)
  => Alp x e1
  -> Alp x (Set (e1,e2))
  -> Alp x (Set e2)
selectFst = eform2 $
  atomWrapped
    (filterSet' f input fullSet)
    (\(e1,s) -> Set.map snd . Set.filter (\e -> fst e == e1) $ s)
  where f = mkSetFilter "selectFst" $
              from2 $ \args e2 ->
              from2' args $ \e1 s ->
              member (e1 &&& e2) s

selectSnd
  :: (Avs x, Avs e2, SetMd (e1,e2), SetMd e1, SMTDefinable (MVFun (Rep e2) (Rep (Set (e1,e2)) -> Rep (Set e1) -> Rep (Set e1) -> SBool)), Ord e2)
  => Alp x e2
  -> Alp x (Set (e1,e2))
  -> Alp x (Set e1)
selectSnd e2 s = filterSet' f (e2 &&& s) fullSet
  where f = mkSetFilter "selectFst" $
              from2 $ \args e1 ->
              from2' args $ \e2 s ->
              member (e1 &&& e2) s

allPassSet
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp (a,e) Bool
  -> Alp x a
  -> Alp x (Set e)
  -> Alp x Bool
allPassSet n p arg set = isFullSet $ filterSet n p arg set

nonePassSet
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp (a,e) Bool
  -> Alp x a
  -> Alp x (Set e)
  -> Alp x Bool
nonePassSet n p arg set = isEmptySet $ filterSet n p arg set

somePassSet
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp (a,e) Bool
  -> Alp x a
  -> Alp x (Set e)
  -> Alp x Bool
somePassSet n p arg set = notE $ nonePassSet n p arg set

nonePassSet' :: (Avs x, SetMd e, Avs a) => SetFilter a e -> Alp x a -> Alp x (Set e) -> Alp x Bool
nonePassSet' f arg set = isEmptySet $ filterSet' f arg set

somePassSet' :: (Avs x, SetMd e, Avs a) => SetFilter a e -> Alp x a -> Alp x (Set e) -> Alp x Bool
somePassSet' f arg set = notE $ nonePassSet' f arg set
