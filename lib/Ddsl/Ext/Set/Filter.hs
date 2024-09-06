{-# LANGUAGE FlexibleContexts #-}

module Ddsl.Ext.Set.Filter where

import Ddsl
import Ddsl.Atom
import Ddsl.Ext.Set.Class
import Ddsl.Symbolic
import Ddsl.Term

import Data.SBV
import Data.Set (Set)
import qualified Data.Set as Set

data ArgWit a

data SetFilter arg elem
  = SetFilter
    { setFilterProgram :: Alp (arg, elem) Bool
    , setFilterWitness :: SetWit elem
    , setFilterArgWitness :: ArgWit arg
    , setFilterSymbol :: MVFun (Rep ((arg, Set elem), Set elem)) SBool
    , setFilterName :: String
    }

filtMvw :: (Avs a, SetMd e) => ArgWit a -> SetWit e -> Mvw (Rep ((a, Set e), Set e)) SBool
filtMvw _ _ = mvw

setFilterTheory :: (Avs a, SetMd e) => SetFilter a e -> Theory
setFilterTheory f = rule' (memberTheory (setFilterWitness f) <> alpTheory (setFilterProgram f)) (filterId (setFilterWitness f) (setFilterName f)) $ do
  let w = setFilterWitness f
      wa = setFilterArgWitness f
      member e s = applyMV (memberMvw w) (memberR w) (e,s)
      filt a s1 s2 = applyMV (filtMvw wa w) (setFilterSymbol f) ((a,s1),s2)

  -- Filters are functional: the output is unique.
  axiom $ \(a,(s1,(s2,s3))) ->
    (filt a s1 s2
    .&& filt a s1 s3)
    .=> eqMV s2 s3

  -- Output membership defined by input membership and annotation.
  axiom $ \(s1,(s2,(a,e))) ->
    filt a s1 s2
    .=> (member e s2
         .<=> (member e s1
               .&& alpFlat (setFilterProgram f) (a,e)))

filterId :: (SetMd e) => SetWit e -> String -> String
filterId w n = elementName w ++ "__SetF__" ++ n

mvwF :: (Avs a, SetMd e) => a -> SetWit e -> Mvw (Rep ((a, Set e), Set e)) SBool
mvwF _ _ = mvw

mkSetFilter
  :: (SetMd e, Avs a
     , SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp (a,e) Bool
  -> SetFilter a e
mkSetFilter = mkSetFilter' undefined setWit

mkSetFilter'
  :: (SetMd e, Avs a
     , SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => a
  -> SetWit e
  -> String
  -> Alp (a,e) Bool
  -> SetFilter a e
mkSetFilter' wa w n p = SetFilter
  { setFilterProgram = p
  , setFilterWitness = w
  , setFilterArgWitness = undefined
  , setFilterSymbol = s
  , setFilterName = n
  }
  where
    sname = filterId w n
    s = mkMVFun (mvwF wa w) $ \((a,s1),s2) ->
      applyMV mvw (applyMV mvw (applyMV mvw (uninterpret sname) a) s1) s2

filterSet'
  :: (Avs x, Avs a, SetMd e)
  => SetFilter a e
  -> Alp x a
  -> Alp x (Set e)
  -> Alp x (Set e)
filterSet' f = eform2 $ atomRelTh
  (setFilterTheory f)
  (setFilterSymbol f)
  (\(arg,set) -> Set.filter
    (\e -> alpFun (setFilterProgram f) (arg,e))
    set)

filterSet
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp (a,e) Bool
  -> Alp x a
  -> Alp x (Set e)
  -> Alp x (Set e)
filterSet n p = filterSet' (mkSetFilter n p)

filterSetE
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> (Alp (a,e) a -> Alp (a,e) e -> Alp (a,e) Bool)
  -> Alp x a
  -> Alp x (Set e)
  -> Alp x (Set e)
filterSetE n p = filterSet' (mkSetFilter n (from2 p))
