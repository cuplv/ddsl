{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Ddsl.Ext.Map.Class where

import Ddsl
import Ddsl.Atom
import Ddsl.Ext.Nat
import Ddsl.Ext.Set
import Ddsl.Term

import Data.SBV
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)

mvwM :: (MapMd k v) => MapWit k v -> Mvw (Rep (Map k v)) SBool
mvwM _ = mvw

mvwKV :: (MapMd k v) => MapWit k v -> Mvw (Rep (k, v, Map k v)) SBool
mvwKV _ = mvw

mvwKN :: (MapMd k v) => MapWit k v -> Mvw (Rep (k, Map k v)) SBool
mvwKN _ = mvw

mvwI :: (MapMd k v) => MapWit k v -> Mvw (Rep ((k, v, Map k v), Map k v)) SBool
mvwI _ = mvw

class (SingleVal (Sv (Map k v)), Avs k, Avs v, Ava (Map k v), Ord k, Eq v, SMTDefinable (MVFun (Rep k) (MVFun (Rep v) (MVFun (Rep (Map k v)) SBool))), SMTDefinable (MVFun (Rep k) (MVFun (Rep (Map k v)) SBool)), SMTDefinable (MVFun (Rep k) (MVFun (Rep v) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))) => MapMd k v where
  data MapWit k v
  kvName :: MapWit k v -> String

  emptyMapR :: MapWit k v -> MVFun (Rep (Map k v)) SBool
  emptyMapR w = mkMVFun (mvwM w) . ufMap "emptyMap" $ w

  keyValR :: MapWit k v -> MVFun (Rep (k, v, Map k v)) SBool
  keyValR w = mkMVFun
    (mvwKV w)
    (\(k,(v,m)) ->
       applyMV mvw (applyMV mvw (applyMV mvw (ufMap "keyVal" w) k) v) m)

  keyNullPartR :: MapWit k v -> MVFun (Rep (k, Map k v)) SBool
  keyNullPartR w = mkMVFun
    (mvwKN w)
    (\(k,m) ->
       applyMV mvw (applyMV mvw (ufMap "keyNullPartR" w) k) m)

  mapInsertR :: MapWit k v -> MVFun (Rep ((k, v, Map k v), Map k v)) SBool
  mapInsertR w = mkMVFun
    (mvwI w)
    (\((k,(v,m1)),m2) ->
       applyMV mvw (applyMV mvw (applyMV mvw (applyMV mvw (ufMap "mapInsert" w) k) v) m1) m2)

ufMap :: (MapMd k v, SMTDefinable f) => String -> MapWit k v -> f
ufMap name = uninterpret . (\s -> name ++ "__" ++ s) . kvName

mapWit :: (MapMd k v) => MapWit k v
mapWit = undefined

keyValTheory :: (MapMd k v) => MapWit k v -> Theory
keyValTheory w = rule ("keyVal__" ++ kvName w) $ do
  let
    keyVal k v m = applyMV (mvwKV w) (keyValR w) (k,(v,m))
    keyNull k m = applyMV (mvwKN w) (keyNullPartR w) (k,m)

  -- Inequality means there must exist a key-val in one map and not in
  -- the other.  Note that key-null in one and not the other is not a
  -- sufficient alternative to inequality.  This means that a map that
  -- has no key-val pairs is equal to the empty map, in which every
  -- key is null.
  let hasDist m1 m2 = existsA $ \(k,v) ->
        keyVal k v m1 ./= keyVal k v m2

  axiom $ \(m1,m2) -> neqMV m1 m2 .=> hasDist m1 m2

  -- Unique val for key
  axiom $ \(k,(v1,(v2,m))) ->
    (keyVal k v1 m
     .&& keyVal k v2 m)
    .=> eqMV v1 v2

  -- keyVal excludes keyNull
  axiom $ \(k,(v,m)) -> sNot (keyVal k v m .&& keyNull k m)

emptyMapTheory :: (MapMd k v) => MapWit k v -> Theory
emptyMapTheory w = rule' (keyValTheory w) ("emptyMap__" ++ kvName w) $ do
  let
    keyVal k v m = applyMV (mvwKV w) (keyValR w) (k,(v,m))
    keyNull k m = applyMV (mvwKN w) (keyNullPartR w) (k,m)
    emptyMap = applyMV mvw (emptyMapR w)

  -- Unique empty map
  axiom $ \(m1,m2) ->
    (emptyMap m1 .&& emptyMap m2)
    .=> eqMV m1 m2

  -- Empty map has no key-vals
  axiom $ \(m,(k,v)) ->
    emptyMap m .=> sNot (keyVal k v m)

  -- Empty map has all key-nulls
  axiom $ \(k,m) ->
    emptyMap m .=> keyNull k m

mapInsertTheory :: (MapMd k v) => MapWit k v -> Theory
mapInsertTheory w = rule' (keyValTheory w) ("mapInsert__" ++ kvName w) $ do
  let keyVal k v m = applyMV (mvwKV w) (keyValR w) (k,(v,m))
      keyNull k m = applyMV (mvwKN w) (keyNullPartR w) (k,m)
      mapInsert k v m1 m2 = applyMV (mvwI w) (mapInsertR w) ((k,(v,m1)),m2)

  -- Insert is functional
  axiom $ \(k,(v,(m1,(m2,m3)))) ->
    (mapInsert k v m1 m2
     .&& mapInsert k v m1 m3)
    .=> eqMV m2 m3

  -- Inserts commute on distinct keys
  axiom $ \(k1,(k2,(v1,(v2,(m1,(m2,(m3,(m4,m5)))))))) ->
    (neqMV k1 k2
     .&& mapInsert k1 v1 m1 m2
     .&& mapInsert k2 v2 m2 m3
     .&& mapInsert k2 v2 m1 m4
     .&& mapInsert k1 v1 m4 m5)
    .=> eqMV m3 m5

  -- Insert asserts keyVal (and implicitly asserts not-keyNull)
  axiom $ \(k,(v,(m1,m2))) ->
    mapInsert k v m1 m2
    .=> keyVal k v m2

  -- Insert only affects keyVal for inserted key
  axiom $ \(k1,(k2,(v1,(v2,(m1,m2))))) ->
    (neqMV k1 k2
     .&& mapInsert k1 v1 m1 m2)
    .=> (keyVal k2 v2 m1
         .<=> keyVal k2 v2 m2)

  -- Insert only affects keyNull for inserted key
  axiom $ \(k1,(k2,(v1,(m1,m2)))) ->
    (neqMV k1 k2
     .&& mapInsert k1 v1 m1 m2)
    .=> (keyNull k2 m1
         .<=> keyNull k2 m2)

isEmptyMap :: (Avs x, MapMd k v) => Alp x (Map k v) -> Alp x Bool
isEmptyMap = isEmptyMap' mapWit

isEmptyMap' :: (Avs x, MapMd k v) => MapWit k v -> Alp x (Map k v) -> Alp x Bool
isEmptyMap' w = eform $ atomFunTh
  (emptyMapTheory w)
  (emptyMapR w)
  Map.null

emptyMap :: (Avs x, MapMd k v) => Alp x (Map k v)
emptyMap = emptyMap' mapWit

emptyMap' :: (Avs x, MapMd k v) => MapWit k v -> Alp x (Map k v)
emptyMap' w = atomPredTh
  (emptyMapTheory w)
  (emptyMapR w)
  Map.empty

keyVal
  :: (Avs x, MapMd k v)
  => Alp x k
  -> Alp x v
  -> Alp x (Map k v)
  -> Alp x Bool
keyVal = keyVal' mapWit

keyVal'
  :: (Avs x, MapMd k v)
  => MapWit k v
  -> Alp x k
  -> Alp x v
  -> Alp x (Map k v)
  -> Alp x Bool
keyVal' w = eform3 $ atomFunTh
  (keyValTheory w)
  (keyValR w)
  (\(k,v,m) -> Map.lookup k m == Just v)

keyNullPart
  :: (Avs x, MapMd k v)
  => Alp x k
  -> Alp x (Map k v)
  -> Alp x Bool
keyNullPart = keyNullPart' mapWit

keyNullPart'
  :: (Avs x, MapMd k v)
  => MapWit k v
  -> Alp x k
  -> Alp x (Map k v)
  -> Alp x Bool
keyNullPart' w = eform2 $ atomFunTh
  (keyValTheory w)
  (keyNullPartR w)
  (\(k,m) -> Map.lookup k m == Nothing)

insertMap
  :: (Avs x, MapMd k v)
  => Alp x k
  -> Alp x v
  -> Alp x (Map k v)
  -> Alp x (Map k v)
insertMap = insertMap' mapWit

insertMap'
  :: (Avs x, MapMd k v)
  => MapWit k v
  -> Alp x k
  -> Alp x v
  -> Alp x (Map k v)
  -> Alp x (Map k v)
insertMap' w = eform3 $ atomRelTh
  (mapInsertTheory w)
  (mapInsertR w)
  -- (\(k,(v,m1)) m2 ->
  --    applyMV (mvwI w) (mapInsertR w) (k,(v,(m1,m2))))
  (\(k,v,m) -> Map.insert k v m)

class (MapMd k v, QE k v, SMTDefinable (MVFun (Rep k) (MVFun (Rep (Map k v)) SBool))) => FlatMapMd k v

mvwFlatNull :: (MapMd k v) => MapWit k v -> Mvw (Rep (k, Map k v)) SBool
mvwFlatNull _ = mvw

flatNullR
  :: (FlatMapMd k v)
  => MapWit k v
  -> MVFun (Rep (k, Map k v)) SBool
flatNullR w = mkMVFun
  (mvwFlatNull w)
  (\(k,m) ->
     applyMV mvw (applyMV mvw (ufMap "flatNull" w) k) m)

flatNullTheory :: (FlatMapMd k v) => MapWit k v -> Theory
flatNullTheory w = rule' (keyValTheory w) ("flatNull__" ++ kvName w) $ do
  let keyVal k v m = applyMV (mvwKV w) (keyValR w) (k,(v,m))
      flatNull k m = applyMV mvw (flatNullR w) (k,m)

  -- keyVal implies not null
  axiom $ \(k,(v,m)) ->
    keyVal k v m
    .=> sNot (flatNull k m)

  -- not null implies exists keyVal
  let hasVal k m = existsA $ \v ->
        keyVal k v m

  axiom $ \(k,m) ->
    flatNull k m
    .|| hasVal k m

flatNull'
  :: (Avs x, FlatMapMd k v)
  => MapWit k v
  -> Alp x k
  -> Alp x (Map k v)
  -> Alp x Bool
flatNull' w = eform2 $ atomFunTh
  (flatNullTheory w)
  (flatNullR w)
  (\(k,m) -> Map.lookup k m == Nothing)

flatNull
  :: (Avs x, FlatMapMd k v)
  => Alp x k
  -> Alp x (Map k v)
  -> Alp x Bool
flatNull = flatNull' mapWit


pairSetWit :: (MapMd k (Set v), SetMd (k,v)) => MapWit k (Set v) -> SetWit (k,v)
pairSetWit _ = setWit

valSetWit :: (MapMd k (Set v), SetMd v) => MapWit k (Set v) -> SetWit v
valSetWit _ = setWit

valNatWit :: (MapMd k v, NatMd v) => MapWit k v -> NatWit v
valNatWit _ = natWit

-- mvwFlatSelectV :: (MapMd k v, SetMd k) => MapWit k v -> Mvw (Rep ((v, Map k v), Set k)) SBool
-- mvwFlatSelectV _ = mvw

-- class (MapMd k v, SetMd k, SMTDefinable (MVFun (Rep v) (Rep (Map k v) -> Rep (Set k) -> SBool))) => FlatSelectV k v

-- instance (MapMd k v, SetMd k, SMTDefinable (MVFun (Rep v) (Rep (Map k v) -> Rep (Set k) -> SBool))) => FlatSelectV k v

-- flatSelectVR :: (FlatSelectV k v) => MapWit k v -> MVFun (Rep ((v, Map k v), Set k)) SBool
-- flatSelectVR w = mkMVFun
--   (mvwFlatSelectV w)
--   (\((v,m),s) ->
--      applyMV mvw (applyMV mvw (applyMV mvw (ufMap "flatSelectV" w) v) m) s)

-- flatSelectVRTheory :: (FlatSelectV k v) => MapWit k v -> Theory
-- flatSelectVRTheory w = rule' (keyValTheory w <> memberTheory (valSetWit w)) ("flatSelectV__" ++ kvName w) $ do

--   axiom $ \(k,(v,(m,s))) ->
--     flatSelectV v m s
--     .=> (member k s
--          .<=> keyVal k v m)

class (MapMd k v, SMTDefinable (MVFun (Rep (k, Map k v)) SBool)) => KeyMapTest k v
instance (MapMd k v, SMTDefinable (MVFun (Rep (k, Map k v)) SBool)) => KeyMapTest k v

keyMaybeR
  :: (KeyMapTest k v)
  => MapWit k v
  -> MVFun (Rep (k, Map k v)) SBool
keyMaybeR w = mkMVFun
  (mvwFlatNull w)
  (\(k,m) ->
     applyMV mvw (applyMV mvw (ufMap "keyMaybe" w) k) m)

keyMaybeTheory :: (KeyMapTest k v) => MapWit k v -> Theory
keyMaybeTheory w = rule' (keyValTheory w <> mapInsertTheory w) ("keyMaybe__" ++ kvName w) $ do
  let keyVal k v m = applyMV (mvwKV w) (keyValR w) (k,(v,m))
      keyMaybe k m = applyMV mvw (keyMaybeR w) (k,m)
      insertMap k v m1 m2 = applyMV (mvwI w) (mapInsertR w) ((k,(v,m1)),m2)

  -- keyVal requires keyMaybe
  axiom $ \(k,(v,m)) ->
    keyVal k v m .=> keyMaybe k m

  -- insertMap preserves keyMaybe
  axiom $ \(k1,(k2,(v,(m1,m2)))) ->
    (insertMap k1 v m1 m2 .&& keyMaybe k2 m1)
    .=> keyMaybe k2 m2

  -- Could also say that keyMaybe is false for emptyMap...

keyMaybe'
  :: (Avs x, KeyMapTest k v)
  => MapWit k v
  -> Alp x k
  -> Alp x (Map k v)
  -> Alp x Bool
keyMaybe' w = eform2 $ atomFunTh
  (keyMaybeTheory w)
  (keyMaybeR w)
  (\(k,m) -> Map.lookup k m /= Nothing)

keyMaybe
  :: (Avs x, KeyMapTest k v)
  => Alp x k
  -> Alp x (Map k v)
  -> Alp x Bool
keyMaybe = keyMaybe' mapWit

mvwUnion :: (MapMd k v) => MapWit k v -> Mvw (Rep ((Map k v, Map k v), Map k v)) SBool
mvwUnion _ = mvw

unionMapR :: (FlatMapMd k v) => MapWit k v -> MVFun (Rep ((Map k v, Map k v), Map k v)) SBool
unionMapR w = mkMVFun
  (mvwUnion w)
  (\((m1,m2),m3) ->
     applyMV mvw (applyMV mvw (applyMV mvw (ufMap "unionMap" w) m1) m2) m3)

unionMapTheory :: (FlatMapMd k v) => MapWit k v -> Theory
unionMapTheory w = rule' (keyValTheory w <> flatNullTheory w) ("unionMap__" ++ kvName w) $ do
  let keyVal k v m = applyMV (mvwKV w) (keyValR w) (k,(v,m))
      flatNull k m = applyMV mvw (flatNullR w) (k,m)
      union m1 m2 m3 = applyMV (mvwUnion w) (unionMapR w) ((m1,m2),m3)

  axiom $ \(k,(v,(m1,(m2,m3)))) ->
    keyVal k v m3
    .<=> (keyVal k v m1 .|| (keyVal k v m2 .&& flatNull k m1))

unionMap'
  :: (Avs x, FlatMapMd k v)
  => MapWit k v
  -> Alp x (Map k v)
  -> Alp x (Map k v)
  -> Alp x (Map k v)
unionMap' w = eform2 $ atomRelTh
  (unionMapTheory w)
  (unionMapR w)
  (uncurry Map.union)

unionMap
  :: (Avs x, FlatMapMd k v)
  => Alp x (Map k v)
  -> Alp x (Map k v)
  -> Alp x (Map k v)
unionMap = unionMap' mapWit
