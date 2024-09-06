{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Set.Example where

import Ddsl
import Ddsl.Ext.Set

import Data.SBV (SBV,mkUninterpretedSort)
import Data.Set (Set)

data Term_S
mkUninterpretedSort ''Term_S

instance SingleVal Term_S

data Term = Term Int deriving (Show,Eq,Ord)

instance Avs Term where
  type Rep Term = SBV Term_S

instance Ava Term where
  type Sv Term = Term_S

data Id_S
mkUninterpretedSort ''Id_S

instance SingleVal Id_S

data Id = Id Int deriving (Show,Eq,Ord)

instance Avs Id where
  type Rep Id = SBV Id_S

instance Ava Id where
  type Sv Id = Id_S

data MySet_S
mkUninterpretedSort ''MySet_S

instance SingleVal MySet_S

instance Avs (Set (Term,Id)) where
  type Rep (Set (Term,Id)) = SBV MySet_S

instance Ava (Set (Term,Id)) where
  type Sv (Set (Term,Id)) = MySet_S

instance SetMd (Term,Id) where
  data SetWit (Term,Id)
  elementName _ = "Term__Id"

test1 :: Alp (Term, Id, Set (Term,Id)) Bool
test1 =
  from3 $ \t i s ->
  member (t &&& i) s
  $=> notE (isEmptySet s)

test2 :: Alp (Term,Id) Bool
test2 =
  from2 $ \t i ->
  notE $ member (t &&& i) emptySet

test3 :: Alp (Term, Id, Set (Term,Id)) Bool
test3 =
  from3 $ \t i s ->
  filterSet' f t s $== filterSet' f t s
  where f = mkSetFilter "test3Filter"
              (from2 $ \a e -> fstE e $== a)

test4 :: Alp (Term, Id, Set (Term,Id)) Bool
test4 =
  from3 $ \t i s ->
  (filterSet' f t s $== emptySet)
  $=> notE (member (t &&& i) s)
  where f = mkSetFilter "test4Filter"
              (from2 $ \a e -> fstE e $== a)

-- Test that uniqueness of empty set is implied by axioms
test5 :: Alp (Set (Term,Id), Set (Term,Id)) Bool
test5 =
  from2 $ \s1 s2 ->
  (isEmptySet s1 $/\ isEmptySet s2)
  $=> (s1 $== s2)

-- Test that uniqueness of full set is implied by axioms
test6 :: Alp (Set (Term,Id), Set (Term,Id)) Bool
test6 =
  from2 $ \s1 s2 ->
  (isFullSet s1 $/\ isFullSet s2)
  $=> (s1 $== s2)

testSubsetReflexive :: Alp (Set (Term,Id)) Bool
testSubsetReflexive =
  subset input input

testSubsetTransitive :: Alp (Set (Term,Id), Set (Term,Id), Set (Term,Id)) Bool
testSubsetTransitive =
  from3 $ \s1 s2 s3 ->
  (subset s1 s2 $/\ subset s2 s3) $=> subset s1 s3

testSubsetAntiSymmetric :: Alp (Set (Term,Id), Set (Term,Id)) Bool
testSubsetAntiSymmetric =
  from2 $ \s1 s2 ->
  (subset s1 s2 $/\ subset s2 s1) $=> (s1 $== s2)

testSubsetLarge :: Alp ((Term,Id), Set (Term,Id), Set (Term,Id)) Bool
testSubsetLarge =
  from3 $ \e s1 s2 ->
  (subset s1 s2 $/\ member e s1) $=> member e s2

testSubsetSmall :: Alp ((Term,Id), Set (Term,Id), Set (Term,Id)) Bool
testSubsetSmall =
  from3 $ \e s1 s2 ->
  (subset s1 s2 $/\ notE (member e s2)) $=> notE (member e s1)
