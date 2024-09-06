{-# LANGUAGE FlexibleContexts #-}

module Ddsl.Ext.Map.Filter where

import Ddsl
import Ddsl.Atom
import Ddsl.Ext.Map.Class
import Ddsl.Term

import Data.SBV
import Data.Map (Map)
import qualified Data.Map as Map

data MapArgWit a

data MapFilter a k v
  = MapFilter
    { mapFilterProgram :: Alp (a,k,v) Bool
    , mapFilterWitness :: MapWit k v
    , mapFilterArgWitness :: MapArgWit a
    , mapFilterSymbol :: MVFun (Rep ((a, Map k v), Map k v)) SBool
    , mapFilterName :: String
    }

filterId :: (MapMd k v) => MapWit k v -> String -> String
filterId w n = kvName w ++ "__MapF__" ++ n

filtMvw :: (Avs a, MapMd k v) => MapArgWit a -> MapWit k v -> Mvw (Rep ((a, Map k v), Map k v)) SBool
filtMvw _ _ = mvw

mapFilterTheory :: (Avs a, MapMd k v) => MapFilter a k v -> Theory
mapFilterTheory f = rule' (keyValTheory (mapFilterWitness f) <> alpTheory (mapFilterProgram f)) (filterId (mapFilterWitness f) (mapFilterName f)) $ do
  let w = mapFilterWitness f
      wa = mapFilterArgWitness f
      keyVal k v m = applyMV (mvwKV w) (keyValR w) (k,(v,m))
      filt a m1 m2 = applyMV (filtMvw wa w) (mapFilterSymbol f) ((a,m1),m2)

  -- Filters are functional: the output is unique
  axiom $ \(a,(m1,(m2,m3))) ->
    (filt a m1 m2
     .&& filt a m1 m3)
    .=> eqMV m2 m3

  -- Output membership is defined by input membership and annotation.
  axiom $ \(m1,(m2,(a,(k,v)))) ->
    filt a m1 m2
    .=> (keyVal k v m2
         .<=> (keyVal k v m1
               .&& alpFlat (mapFilterProgram f) (a,(k,v))))

mvwF :: (Avs a, MapMd k v) => a -> MapWit k v -> Mvw (Rep ((a, Map k v), Map k v)) SBool
mvwF _ _ = mvw

mkMapFilter
  :: (MapMd k v, Avs a
     , SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))
  => String
  -> Alp (a,k,v) Bool
  -> MapFilter a k v
mkMapFilter = mkMapFilter' undefined mapWit

mkMapFilter'
  :: (MapMd k v, Avs a
     , SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))
  => a
  -> MapWit k v
  -> String
  -> Alp (a,k,v) Bool
  -> MapFilter a k v
mkMapFilter' wa w n p = MapFilter
  { mapFilterProgram = p
  , mapFilterWitness = w
  , mapFilterArgWitness = undefined
  , mapFilterSymbol = s
  , mapFilterName = n
  }
  where
    sname = filterId w n
    s = mkMVFun (mvwF wa w) $ \((a,s1),s2) -> applyMV mvw (applyMV mvw (applyMV mvw (uninterpret sname) a) s1) s2

filterMap'
  :: (Avs x, Avs a, MapMd k v)
  => MapFilter a k v
  -> Alp x a
  -> Alp x (Map k v)
  -> Alp x (Map k v)
filterMap' f = eform2 $ atomRelTh
  (mapFilterTheory f)
  (mapFilterSymbol f)
  (\(a,m) -> Map.filterWithKey
    (\k v -> alpFun (mapFilterProgram f) (a,k,v))
    m)

filterMap
  :: (Avs x, Avs a, MapMd k v, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))
  => String
  -> Alp (a,k,v) Bool
  -> Alp x a
  -> Alp x (Map k v)
  -> Alp x (Map k v)
filterMap n p = filterMap' (mkMapFilter n p)

filterMapE
  :: (Avs x, Avs a, MapMd k v, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))
  => String
  -> (Alp (a,k,v) a -> Alp (a,k,v) k -> Alp (a,k,v) v -> Alp (a,k,v) Bool)
  -> Alp x a
  -> Alp x (Map k v)
  -> Alp x (Map k v)
filterMapE n p = filterMap' (mkMapFilter n (from3 p))
