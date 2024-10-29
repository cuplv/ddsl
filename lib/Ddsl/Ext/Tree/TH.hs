{-# LANGUAGE TemplateHaskell #-}

module Ddsl.Ext.Tree.TH
  ( mkKtTreeMd
  ) where

import Ddsl
import Ddsl.TH
import Ddsl.Ext.Tree.Class

import Data.SBV (SBV)
import Language.Haskell.TH

mkKtTreeMd :: String -> Name -> Name -> Name -> Q [Dec]
mkKtTreeMd s branchName indexName entryName = do
  let
    branchType = ConT branchName
    indexType = ConT indexName
    entryType = ConT entryName
    keyName = mkName $ "S__KtTreeKey__" ++ s
    keyType = AppT (AppT (ConT $ mkName "KtKey") branchType) indexType
    keyDecl = DataD [] keyName [] Nothing [] []
    bodyName = mkName $ "S__KtTreeBody__" ++ s
    bodyType = AppT (AppT (AppT (ConT $ mkName "KtTree") branchType) indexType) entryType
    bodyDecl = DataD [] bodyName [] Nothing [] []

  xDeclKey <- mkSort keyName
  xDeclBody <- mkSort bodyName

  iDecl <- [d|instance SingleVal $(conT keyName)
              instance Avs (KtKey $(conT branchName) $(conT indexName)) where
                type Rep (KtKey $(conT branchName) $(conT indexName)) = SBV $(conT keyName)
              instance Ava (KtKey $(conT branchName) $(conT indexName)) where
                type Sv (KtKey $(conT branchName) $(conT indexName)) = $(conT keyName)
              instance SingleVal $(conT bodyName)
              instance Avs (KtTree $(conT branchName) $(conT indexName) $(conT entryName)) where
                type Rep (KtTree $(conT branchName) $(conT indexName) $(conT entryName)) = SBV $(conT bodyName)
              instance Ava (KtTree $(conT branchName) $(conT indexName) $(conT entryName)) where
                type Sv (KtTree $(conT branchName) $(conT indexName) $(conT entryName)) = $(conT bodyName)
              instance KtTreeMd $(conT branchName) $(conT indexName) $(conT entryName) where
                data KtTreeWit $(conT branchName) $(conT indexName) $(conT entryName)
                ktTreeName _ = s
           |]

  return $ [keyDecl,bodyDecl] ++ xDeclKey ++ xDeclBody ++ iDecl
