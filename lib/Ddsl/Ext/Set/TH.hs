{-# LANGUAGE TemplateHaskell #-}

module Ddsl.Ext.Set.TH
  ( mkSetMd
  ) where

import Ddsl
import Ddsl.TH
import Ddsl.Ext.Set.Class

import Data.Set (Set)
import Data.SBV (SBV)
import Language.Haskell.TH

{- | Declare a Rail type for a 'Data.Set.Set'. To use this, you need to
   enable the following language extensions:

   @
   LANGUAGE DeriveAnyClass
   LANGUAGE DeriveDataTypeable
   LANGUAGE FlexibleInstances
   LANGUAGE MultiParamTypeClasses
   LANGUAGE StandaloneDeriving
   LANGUAGE TemplateHaskell
   LANGUAGE TypeFamilies
@

   Then write, for example:

   @mkSetMd \"Int\" ''Int@

   to declare a Rail type for @'Data.Set.Set' 'Int'@,
   assuming that you have already declared a Rail type for 'Int'.
-}
mkSetMd :: String -> Name -> Q [Dec]
mkSetMd s en = do
  let
    etype = ConT en
    sname = mkName $ "S__Set__" ++ s
    mtype = AppT (ConT $ mkName "Set") etype
    dDecl = DataD [] sname [] Nothing [] []

  xDecl <- mkSort sname

  iDecl <- [d|instance SingleVal $(conT sname)
              instance Avs (Set $(conT en)) where
                type Rep (Set $(conT en)) = SBV $(conT sname)
              instance Ava (Set $(conT en)) where
                type Sv (Set $(conT en)) = $(conT sname)
              instance SetMd $(conT en) where
                data SetWit $(conT en)
                elementName _ = s
           |]

  return $ [dDecl] ++ xDecl ++ iDecl
