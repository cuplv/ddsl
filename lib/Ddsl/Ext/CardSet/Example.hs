{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.CardSet.Example where

import Ddsl
import Ddsl.Ext.CardSet
import Ddsl.Ext.Nat
import Ddsl.Ext.Set

import Data.Set (Set)
import qualified Data.Set as Set

newtype X = X Int deriving (Show,Eq,Ord)

mkDType "X" ''X

newtype C = C Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)

mkNatMd "C" ''C

mkSetMd "XSet" ''X

instance CardSetMd C X

test1 :: Alp (C, C, Set X, Set X, Set X) Bool
test1 =
  from5 $ \c1 c2 s1 s2 s3 ->
  (ltSum (card s3) c1 c2
   $/\ (c1 $<= commonCard s1 s3)
   $/\ (c2 $<= commonCard s2 s3))
  $=>
  (somePassSet
     "s3filter"
     (from2 $ \args e ->
        from2' args $ \s1 s2 ->
        member e s1 $/\ member e s2)
     (tup2 s1 s2)
     s3)
