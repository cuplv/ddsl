{-# LANGUAGE TemplateHaskell #-}

module Ddsl.Ext.List.TH
  ( mkListMd
  ) where

import Ddsl
import Ddsl.TH
import Ddsl.Ext.List.Class

import Data.SBV (SBV)
import Language.Haskell.TH

mkListMd :: String -> Name -> Name -> Q [Dec]
mkListMd s indexName elementName = do
  let
    indexType = ConT indexName
    elementType = ConT elementName
    sname = mkName $ "S__List__" ++ s
    mtype = AppT (AppT (ConT $ mkName "List") indexType) elementType
    dDecl = DataD [] sname [] Nothing [] []

  xDecl <- mkSort sname

  iDecl <- [d|instance SingleVal $(conT sname)
              instance Avs (List $(conT indexName) $(conT elementName)) where
                type Rep (List $(conT indexName) $(conT elementName)) = SBV $(conT sname)
              instance Ava (List $(conT indexName) $(conT elementName)) where
                type Sv (List $(conT indexName) $(conT elementName)) = $(conT sname)
              instance ListMd $(conT indexName) $(conT elementName) where
                data ListWit $(conT indexName) $(conT elementName)
                listName _ = s
           |]

  return $ [dDecl] ++ xDecl ++ iDecl
