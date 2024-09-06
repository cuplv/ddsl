{-# LANGUAGE TemplateHaskell #-}

module Ddsl.Ext.Map.TH
  ( mkMapMd
  ) where

import Ddsl
import Ddsl.TH
import Ddsl.Ext.Map.Class

import Data.Map (Map)
import Data.SBV (SBV)
import Language.Haskell.TH

{- | Declare a Rail type for a 'Data.Map.Map'. To use this, you need to
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

   @mkMapMd \"Int_String\" ''Int ''String@

   to declare a Rail type for @'Data.Map.Map' 'Int' 'String'@,
   assuming that you have already declared Rail types for 'Int' and
   'String'.
-}
mkMapMd :: String -> Name -> Name -> Q [Dec]
mkMapMd s kn vn = do
  let
    ktype = ConT kn
    vtype = ConT vn
    sname = mkName $ "S__Map__" ++ s
    mtype = AppT (AppT (ConT $ mkName "Map") ktype) vtype
    dDecl = DataD [] sname [] Nothing [] []

  xDecl <- mkSort sname

  iDecl <- [d|instance SingleVal $(conT sname)
              instance Avs (Map $(conT kn) $(conT vn)) where
                type Rep (Map $(conT kn) $(conT vn)) = SBV $(conT sname)
              instance Ava (Map $(conT kn) $(conT vn)) where
                type Sv (Map $(conT kn) $(conT vn)) = $(conT sname)
              instance MapMd $(conT kn) $(conT vn) where
                data MapWit $(conT kn) $(conT vn)
                kvName _ = s
           |]

  return $ [dDecl] ++ xDecl ++ iDecl
