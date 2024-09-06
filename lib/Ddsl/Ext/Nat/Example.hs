{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Nat.Example where

import Ddsl
import Ddsl.Ext.Nat

import Data.SBV (SBV,mkUninterpretedSort)

newtype N = N Int
  deriving (Show,Eq,Ord)
  deriving newtype (Num)

mkNatMd "N" ''N
