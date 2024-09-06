{-# LANGUAGE TemplateHaskell #-}

module Ddsl.Ext.Nat.TH
  ( mkNatMd
  ) where

import Ddsl
import Ddsl.TH
import Ddsl.Ext.Nat.Class

import Data.SBV (SBV)
import Language.Haskell.TH

{- | Declare a type to be a 'NatMd'. To use this, you need to
   enable the following language extensions:

   @
   LANGUAGE DeriveAnyClass
   LANGUAGE DeriveDataTypeable
   LANGUAGE StandaloneDeriving
   LANGUAGE TemplateHaskell
   LANGUAGE TypeFamilies
@

   Then write, for example:

   @mkNatMd \"Int\" ''Int@

   to declare a 'Int' to be a  'NatMd'.
-}
mkNatMd :: String -> Name -> Q [Dec]
mkNatMd s n = do
  d1 <- mkDType s n
  d2 <- [d|instance NatMd $(conT n) where
             data NatWit $(conT n)
             natName _ = s
        |]
  return $ d1 ++ d2
