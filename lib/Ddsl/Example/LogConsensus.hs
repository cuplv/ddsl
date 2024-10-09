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

-- | A record of accepts
type Accepts = Accum (Branch,NodeId) Index

type State = (Voters, Votes, Ktl, AMap)
