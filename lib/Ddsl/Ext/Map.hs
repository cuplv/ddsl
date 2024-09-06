{-# LANGUAGE FlexibleContexts #-}

module Ddsl.Ext.Map
  ( MapMd (..)
  , Map
  , mkMapMd
  , emptyMap
  , isEmptyMap
  , keyVal
  -- , keyValGe
  , keyMaybe
  , keyNull
  , keyNullPart
  , selectV
  , insertMap
  , unionMap
  , submap
  , subkey
  , FlatMapMd (..)
  , flatNull
  , allKeys
  , MapFilter
  , mkMapFilter
  , filterMap
  , filterMapE
  , filterMap'
  , allPassMap
  , allPassMap'
  , somePassMap
  , somePassMap'
  , nonePassMap
  , nonePassMap'
  ) where

import Ddsl
import Ddsl.Atom (atomWrapped)
import Ddsl.Ext.Map.Class
import Ddsl.Ext.Map.Filter
import Ddsl.Ext.Map.TH
import Ddsl.Ext.Set

import Data.Map (Map)
import qualified Data.Map as Map
import Data.SBV (SMTDefinable,SBool)

allPassMap :: (Avs x, MapMd k v, Avs a, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool)))) => String -> Alp (a,k,v) Bool -> Alp x a -> Alp x (Map k v) -> Alp x Bool
allPassMap n p arg map = map $== filterMap n p arg map

allPassMap' :: (Avs x, MapMd k v, Avs a) => MapFilter a k v -> Alp x a -> Alp x (Map k v) -> Alp x Bool
allPassMap' f arg map = map $== filterMap' f arg map

nonePassMap :: (Avs x, MapMd k v, Avs a, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool)))) => String -> Alp (a,k,v) Bool -> Alp x a -> Alp x (Map k v) -> Alp x Bool
nonePassMap n p arg map = isEmptyMap $ filterMap n p arg map

nonePassMap' :: (Avs x, MapMd k v, Avs a) => MapFilter a k v -> Alp x a -> Alp x (Map k v) -> Alp x Bool
nonePassMap' f arg map = isEmptyMap $ filterMap' f arg map

somePassMap :: (Avs x, MapMd k v, Avs a, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool)))) => String -> Alp (a,k,v) Bool -> Alp x a -> Alp x (Map k v) -> Alp x Bool
somePassMap n p arg map = notE $ nonePassMap n p arg map

somePassMap' :: (Avs x, MapMd k v, Avs a) => MapFilter a k v -> Alp x a -> Alp x (Map k v) -> Alp x Bool
somePassMap' f arg map = notE $ nonePassMap' f arg map

keyNull
  :: (Avs x, MapMd k v, SMTDefinable (MVFun (Rep k) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))
  => Alp x k
  -> Alp x (Map k v)
  -> Alp x Bool
keyNull k m =
  let f = mkMapFilter "keyNotNull"
            (from3 $ \nullKey k' _ -> nullKey $== k')
  in nonePassMap' f k m

selectV
  :: (Avs x, MapMd k v, SetMd k, SMTDefinable (MVFun (Rep v) (MVFun (Rep (Map k v)) (MVFun (Rep (Set k)) (MVFun (Rep (Set k)) SBool)))))
  => Alp x v
  -> Alp x (Map k v)
  -> Alp x (Set k)
selectV = eform2 $
  let f = mkSetFilter "selectV"
            (from2 $ \args k ->
             from2' args $ \v m ->
             keyVal k v m)
  in atomWrapped
       (filterSet' f input fullSet)
       (\(cv,cm) -> Map.keysSet . Map.filter (== cv) $ cm)

allKeys :: (Avs x, SetMd k, FlatMapMd k v) => Alp x (Map k v) -> Alp x (Set k)
allKeys m = filterSet' f m fullSet
  where f = mkSetFilter "allKeys" $
          from2 $ \m e -> notE (flatNull e m)

submap :: (Avs x, MapMd k v) => Alp x (Map k v) -> Alp x (Map k v) -> Alp x Bool
submap m1 m2 = allPassMap' f m2 m1
  where f = mkMapFilter "submap" (from3 $ \m k v -> keyVal k v m)

subkey
  :: ( Avs x
     , MapMd k v
     , SMTDefinable (MVFun (Rep k) (Rep (Map k v) -> Rep (Map k v) -> Rep (Map k v) -> SBool)))
  => Alp x k -> Alp x (Map k v) -> Alp x (Map k v) -> Alp x Bool
subkey k m1 m2 = allPassMap "subkey"
  (from3 $ \args k v ->
   from2' args $ \kArg m2 ->
   (k $== kArg) $=> keyVal k v m2)
  (k &&& m2)
  m1
