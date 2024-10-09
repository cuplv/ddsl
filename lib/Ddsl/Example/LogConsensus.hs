{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Example.LogConsensus where

import Ddsl.Prelude

import Prelude (print,putStr,(=<<),Num,String)

import Data.SBV (SBV,mkUninterpretedSort)

-----------
-- TYPES --
-----------

-- | A node identifier (which is just an 'Int').
newtype NodeId = NodeId Int deriving (Show,Eq,Ord)
-- Declare an opaque symbolic representation for 'NodeId'.
mkDType "NodeId" ''NodeId

-- | A term (also just an 'Int').
newtype Branch = Branch Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Branch'.
mkNatMd "Branch" ''Branch
-- We'll reason about sets of terms, so we declare this as well.
mkSetMd "Branch" ''Branch

-- | An index (also just an 'Int').
newtype Index = Index Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)
-- Declare a symbolic representation, with Nat operations, for 'Branch'.
mkNatMd "Index" ''Index

-- | A set of nodes eligible to vote.
type Voters = Set NodeId
-- Declare a symbolic representation for sets of 'NodeID's.
mkSetMd "NodeId" ''NodeId

-- | A voting node in a particular term
type VoterId = (Branch,NodeId)
-- | A record of votes
type Votes = Map VoterId NodeId
-- Declare a symbolic representation for the Votes map.
mkMapMd "Branch_NodeId_NodeId" ''VoterId ''NodeId

-- | An entry in the log (actually just a 'String')
newtype Entry = Entry String
  deriving (Show,Eq,Ord)
mkDType "Entry" ''Entry

-- | A record of accepts
type Accepts = Accum (Branch,NodeId) Index

-- Tree stuff 

data Log_S
mkUninterpretedSort ''Log_S
data LK_S
mkUninterpretedSort ''LK_S
data LT_S
mkUninterpretedSort ''LT_S

instance SingleVal Log_S

type Log = List Index Entry

instance Avs Log where
  type Rep Log = SBV Log_S

instance Ava Log where
  type Sv Log = Log_S

instance ListMd Index Entry where
  data ListWit Index Entry
  listName _ = "Index__Entry"

instance SingleVal LK_S

type LK = KtKey Branch Index

instance Avs LK where
  type Rep LK = SBV LK_S

instance Ava LK where
  type Sv LK = LK_S

instance SingleVal LT_S

type LT = KtTree Branch Index Entry

instance Avs LT where
  type Rep LT = SBV LT_S

instance Ava LT where
  type Sv LT = LT_S

type Tree = KtTree Branch Index Entry
instance KtTreeMd Branch Index Entry where
  data KtTreeWit Branch Index Entry
  ktTreeName _ = "KtLog"

type State = (Voters, Votes, Tree, Accepts)
