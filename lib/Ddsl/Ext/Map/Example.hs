{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Map.Example where

import Ddsl
import Ddsl.Ext.Map
import Ddsl.Ext.Set

import Data.SBV (SBV,mkUninterpretedSort,uninterpret)
import Data.Map (Map)
import Data.Set (Set)

data Term_S
mkUninterpretedSort ''Term_S

instance SingleVal Term_S

data Term = Term Int deriving (Show,Eq,Ord)

instance Avs Term where
  type Rep Term = SBV Term_S

instance Ava Term where
  type Sv Term = Term_S

data TermSet_S
mkUninterpretedSort ''TermSet_S

instance SingleVal TermSet_S

instance Avs (Set Term) where
  type Rep (Set Term) = SBV TermSet_S

instance Ava (Set Term) where
  type Sv (Set Term) = TermSet_S

instance SetMd Term where
  data SetWit Term
  elementName _ = "Term"

data Index_S
mkUninterpretedSort ''Index_S

instance SingleVal Index_S

data Index = Index Int deriving (Show,Eq,Ord)

instance Avs Index where
  type Rep Index = SBV Index_S

instance Ava Index where
  type Sv Index = Index_S

data Id_S
mkUninterpretedSort ''Id_S

instance SingleVal Id_S

data Id = Id Int deriving (Show,Eq,Ord)

instance Avs Id where
  type Rep Id = SBV Id_S

instance Ava Id where
  type Sv Id = Id_S

data MyMap_S
mkUninterpretedSort ''MyMap_S

instance SingleVal MyMap_S

instance Avs (Map (Term,Id) Index) where
  type Rep (Map (Term,Id) Index) = SBV MyMap_S

instance Ava (Map (Term,Id) Index) where
  type Sv (Map (Term,Id) Index) = MyMap_S

instance MapMd (Term,Id) Index where
  data MapWit (Term,Id) Index
  kvName _ = "Term_Id__Index"

data IdSet_S
mkUninterpretedSort ''IdSet_S

instance SingleVal IdSet_S

instance Avs (Set Id) where
  type Rep (Set Id) = SBV IdSet_S

instance Ava (Set Id) where
  type Sv (Set Id) = IdSet_S

instance SetMd Id where
  data SetWit Id
  elementName _ = "Id"

data MySet_S
mkUninterpretedSort ''MySet_S

instance SingleVal MySet_S

instance Avs (Set (Term,Id)) where
  type Rep (Set (Term,Id)) = SBV MySet_S

instance Ava (Set (Term,Id)) where
  type Sv (Set (Term,Id)) = MySet_S

instance SetMd (Term,Id) where
  data SetWit (Term,Id)
  elementName _ = "Term_Id"

data MyMap2_S
mkUninterpretedSort ''MyMap2_S

instance SingleVal MyMap2_S

instance Avs (Map Term (Set Id)) where
  type Rep (Map Term (Set Id)) = SBV MyMap2_S

instance Ava (Map Term (Set Id)) where
  type Sv (Map Term (Set Id)) = MyMap2_S

instance MapMd Term (Set Id) where
  data MapWit Term (Set Id)
  kvName _ = "Term__Id"

instance QE Term (Set Id)

instance FlatMapMd Term (Set Id)

test1 :: Alp (Term, Id, Index, Map (Term,Id) Index) Bool
test1 =
  from4 $ \t i x m ->
  insertMap (t &&& i) x m
  $/= emptyMap

test3 :: Alp (Term, Id, Index, Map (Term,Id) Index) Bool
test3 =
  from4 $ \t i x m ->
  filterMap' f (t &&& x) m $== filterMap' f (t &&& x) m
  where f = mkMapFilter "test3Filter"
              (from3 $ \a k v ->
                  (fstE k $== fstE a)
                  $/\ (v $== sndE a))

test4 :: Alp (Term, Id, Index, Map (Term,Id) Index) Bool
test4 =
  from4 $ \t i x m ->
  (filterMap' f (t &&& x) m $== emptyMap)
  $=> notE (keyVal (t &&& i) x m)
  where f = mkMapFilter "test4Filter"
              (from3 $ \a k v ->
                  (fstE k $== fstE a)
                  $/\ (v $== sndE a))

-- -- Falsifies on mio in 86.457s with MBQI, 86.748s without
-- test5 :: Alp ((Term, Set Id), Term, Id, Set (Term,Id)) Bool
-- test5 =
--   from4 $ \args t i s ->
--   from2' args $ \t' v' ->
--   letb (insertMap t' v' $ pairMap s) $ \m ->
--   (member (t &&& i) s
--    $/\ (emptySet $/= allKeys m)
--   )
--   $=> keyNull t m
