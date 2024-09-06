{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Accum.Example where

import Ddsl
import Ddsl.Ext.Accum
import Ddsl.Ext.ForallCheck
import Ddsl.Ext.Nat

import Data.SBV (SBV,mkUninterpretedSort,uninterpret)

newtype Term = Term Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
mkNatMd "Term" ''Term

newtype Rid = Rid Int deriving (Show,Eq,Ord)
mkDType "Rid" ''Rid

newtype Index = Index Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
mkNatMd "Index" ''Index

type TermRid = (Term,Rid)

mkAccumMd "Index_Rid" ''TermRid ''Index

instance QE (Index, Accum (Term,Rid) Index) (Term,Rid)

instance QE (Index, Accum (Term,Rid) Index, Accum (Term,Rid) Index) (Term,Rid)


test1 :: Alp (Accum (Term,Rid) Index, Term, Rid, Index, Index) Bool
test1 =
  from5 $ \m t r i1 i2 ->
  let c i m = checkForall "test1"
        (from2 $ \args e -> notE (upTo e (fstE args) (sndE args)))
        (i &&& m)
  in (c i1 m $/\ notE (c i1 (advance (t &&& r) i2 m)))
     $=> (i1 $<= i2)

test2 :: Alp (Accum (Term,Rid) Index, Term, Rid, Index, Index) Bool
test2 =
  from5 $ \m1 t r i1 i2 ->
  letb (advance (t &&& r) i2 m1) $ \m2 ->
  checkExists "test2"
    (from2 $ \args e ->
     from3' args $ \i m1 m2 ->
     upTo e i m2
     $=> upTo e i m1)
    (tup3 i1 m1 m2)
  $=> (i1 $<= i2)

test3 :: Alp (Accum (Term,Rid) Index, (Term, Rid), (Term, Rid), Index, Index) Bool
test3 =
  from5 $ \m1 k1 k2 i1 i2 ->
  letb (advance k1 i2 m1) $ \m2 ->
  (notE (upTo k2 i1 m1)
   $/\ upTo k2 i1 m2)
  $=> ((i1 $<= i2) $/\ (k1 $== k2))
