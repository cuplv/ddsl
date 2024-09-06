{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Accum.Class
  ( Accum (..)
  , AccumMd (accumName)
  , AccumWit
  , accumWit
  , upTo
  , advance
  , accumMono
  -- * Low-level
  , upToR
  , advanceR
  , upToTheory
  , advanceTheory
  , accumMonoTheory
  )where

import Ddsl
import Ddsl.Atom
import Ddsl.Ext.Nat
import Ddsl.Term

import Data.Map (Map)
import qualified Data.Map as Map
import Data.SBV

data Accum k v = Accum (Map k v) deriving (Show,Eq,Ord)

mvwUpTo :: (AccumMd k v) => AccumWit k v -> Mvw (Rep (k, v, Accum k v)) SBool
mvwUpTo _ = mvw

mvwAdvance :: (AccumMd k v) => AccumWit k v -> Mvw (Rep ((k,v,Accum k v), Accum k v)) SBool
mvwAdvance _ = mvw

class (Ord k, Avs k, Avs v, Ava (Accum k v), SMTDefinable (MVFun (Rep k) (MVFun (Rep v) (Rep (Accum k v) -> SBool))), SMTDefinable (MVFun (Rep k) (MVFun (Rep v) (Rep (Accum k v) -> Rep (Accum k v) -> SBool)))) => AccumMd k v where
  data AccumWit k v
  accumName :: AccumWit k v -> String

  upToR :: AccumWit k v -> MVFun (Rep (k, v, Accum k v)) SBool
  upToR w = mkMVFun
    (mvwUpTo w)
    (\(k,(v,m)) ->
       applyMV mvw (applyMV mvw (applyMV mvw (ufAccum "upTo" w) k) v) m)

  advanceR :: AccumWit k v -> MVFun (Rep ((k, v, Accum k v), Accum k v)) SBool
  advanceR w = mkMVFun
    (mvwAdvance w)
    (\((k,(v,m1)),m2) ->
       applyMV mvw (applyMV mvw (applyMV mvw (applyMV mvw (ufAccum "advance" w) k) v) m1) m2)

ufAccum :: (AccumMd k v, SMTDefinable f) => String -> AccumWit k v -> f
ufAccum name = uninterpret . (\s -> name ++ "__" ++ s) . accumName

accumWit :: (AccumMd k v) => AccumWit k v
accumWit = undefined

valWit :: (AccumMd k v, NatMd v) => AccumWit k v -> NatWit v
valWit _ = natWit

upToTheory :: (AccumMd k v, NatMd v) => AccumWit k v -> Theory
upToTheory w = rule' (zeroNatTheory (valWit w) <> leNatTheory (valWit w)) ("upTo__" ++ accumName w) $ do
  let upTo k v m = applyMV (mvwUpTo w) (upToR w) (k,(v,m))
      isZero = applyMV mvw (isZeroR (valWit w))
      le a1 a2 = applyMV (leMvw (valWit w)) (leNatR (valWit w)) (a1,a2)

  -- All keys are always up to zero
  axiom $ \(k,(v,m)) -> isZero v .=> upTo k v m

  -- upTo greater implies upTo lesser
  axiom $ \(k,(v1,(v2,m))) ->
    (le v1 v2
     .&& upTo k v2 m)
    .=> upTo k v1 m

advanceTheory :: (AccumMd k v, NatMd v) => AccumWit k v -> Theory
advanceTheory w = rule' (upToTheory w <> accumMonoTheory w <> leNatTheory (valWit w)) ("advance__" ++ accumName w) $ do
  let upTo k v m = applyMV (mvwUpTo w) (upToR w) (k,(v,m))
      advance k v m1 m2 = applyMV (mvwAdvance w) (advanceR w) ((k,(v,m1)),m2)
      le a1 a2 = applyMV (leMvw (valWit w)) (leNatR (valWit w)) (a1,a2)
      accumMono m1 m2 = applyMV (mvwAccumMono w) (accumMonoR w) (m1,m2)

  -- Advance is deterministic
  axiom $ \(k,(v,(m1,(m2,m3)))) ->
    (advance k v m1 m2 .&& advance k v m1 m3)
    .=> (eqMV m1 m2)

  -- Advance doesn't touch other keys
  axiom $ \(k1,(v,(m1,(m2,k2)))) ->
    (advance k1 v m1 m2 .&& sNot (eqMV k1 k2))
    .=> (upTo k2 v m1
         .<=> upTo k2 v m2)

  -- Advance implies up-to for less-or-equal values
  axiom $ \(k,(v1,(v2,(m1,m2)))) ->
    (advance k v2 m1 m2 .&& le v1 v2)
    .=> upTo k v1 m2

  -- Advance preserves up-to for all values
  axiom $ \(k,(v1,(v2,(m1,m2)))) ->
    (advance k v1 m1 m2 .&& upTo k v2 m1)
    .=> upTo k v2 m2

  -- Advance preserves not-up-to for greater values
  axiom $ \(k,(v1,(v2,(m1,m2)))) ->
    (advance k v1 m1 m2
     .&& le v1 v2
     .&& sNot (eqMV v1 v2) -- v1 < v2
     .&& sNot (upTo k v2 m1))
    .=> sNot (upTo k v2 m2)

  -- Advance preserves accumMono
  axiom $ \(k,(v,(m1,m2))) ->
    advance k v m1 m2
    .=> accumMono m1 m2

upTo'
  :: (Avs x, AccumMd k v, NatMd v)
  => AccumWit k v
  -> Alp x k
  -> Alp x v
  -> Alp x (Accum k v)
  -> Alp x Bool
upTo' w = eform3 $ atomFunTh
  (upToTheory w)
  (upToR w)
  (\(k,v,Accum m) -> case Map.lookup k m of
      Just v' -> v' >= v
      Nothing -> False)

upTo
  :: (Avs x, AccumMd k v, NatMd v)
  => Alp x k
  -> Alp x v
  -> Alp x (Accum k v)
  -> Alp x Bool
upTo = upTo' accumWit

advance'
  :: (Avs x, AccumMd k v, NatMd v)
  => AccumWit k v
  -> Alp x k
  -> Alp x v
  -> Alp x (Accum k v)
  -> Alp x (Accum k v)
advance' w = eform3 $ atomRelTh
  (advanceTheory w)
  (advanceR w)
  (\(k,v,Accum m) -> Accum $
    case Map.lookup k m of
      Just v' | v' >= v -> m
      _ -> Map.insert k v m)

advance
  :: (Avs x, AccumMd k v, NatMd v)
  => Alp x k
  -> Alp x v
  -> Alp x (Accum k v)
  -> Alp x (Accum k v)
advance = advance' accumWit

-- The key has the same value on the left and right sides.
accumMatch
  :: (Avs x, AccumMd k v)
  => Alp x k
  -> Alp x (Accum k v)
  -> Alp x (Accum k v)
  -> Alp x Bool
accumMatch = undefined

mvwAccumMono :: (AccumMd k v) => AccumWit k v -> Mvw (Rep (Accum k v, Accum k v)) SBool
mvwAccumMono _ = mvw

accumMonoR :: (AccumMd k v) => AccumWit k v -> MVFun (Rep (Accum k v, Accum k v)) SBool
accumMonoR w = mkMVFun
  (mvwAccumMono w)
  (\(m1,m2) -> applyMV mvw (applyMV mvw (ufAccum "accumMono" w) m1) m2)

accumMonoTheory :: (AccumMd k v, NatMd v) => AccumWit k v -> Theory
accumMonoTheory w = rule' (upToTheory w) ("accumMono__" ++ accumName w) $ do
  let upTo k v m = applyMV (mvwUpTo w) (upToR w) (k,(v,m))
      le a1 a2 = applyMV (leMvw (valWit w)) (leNatR (valWit w)) (a1,a2)
      accumMono m1 m2 = applyMV (mvwAccumMono w) (accumMonoR w) (m1,m2)

  -- accumMono and upTo
  axiom $ \(k,(v,(m1,m2))) ->
    (accumMono m1 m2 .&& upTo k v m1)
    .=> upTo k v m2

  -- Reflexive
  axiom $ \m -> accumMono m m

  -- Transitive
  axiom $ \(m1,(m2,m3)) ->
    (accumMono m1 m2 .&& accumMono m2 m3)
    .=> accumMono m1 m3

  -- Anti-symmetric
  axiom $ \(m1,m2) ->
    (accumMono m1 m2 .&& accumMono m2 m1)
    .=> eqMV m1 m2

-- All keys in the left-side have greater than or equal to values on
-- the right side.
accumMono
  :: (Avs x, AccumMd k v, NatMd v)
  => Alp x (Accum k v)
  -> Alp x (Accum k v)
  -> Alp x Bool
accumMono = accumMono' accumWit

accumMono'
  :: (Avs x, AccumMd k v, NatMd v)
  => AccumWit k v
  -> Alp x (Accum k v)
  -> Alp x (Accum k v)
  -> Alp x Bool
accumMono' w = eform2 $ atomFunTh
  (accumMonoTheory w)
  (accumMonoR w)
  (error "accumMono not runtime-implemented.")
