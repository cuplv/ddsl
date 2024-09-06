{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.TH
  ( mkSort
  , mkDType
  ) where

import Ddsl.Symbolic
import qualified Language.Haskell.TH as TH

import Data.Generics
import Data.SBV

mkSort :: TH.Name -> TH.Q [TH.Dec]
mkSort typeName = do
    let typeCon = TH.conT typeName

    derives <- [d| deriving instance Show     $typeCon
                   deriving instance Read     $typeCon
                   deriving instance Data     $typeCon
                   deriving instance SymVal   $typeCon
                   deriving instance HasKind  $typeCon
                   deriving instance SatModel $typeCon
               |]


    sType <- TH.conT ''SBV `TH.appT` typeCon

    let declConstructor c = ((nm, bnm), [sig, def])
          where bnm  = TH.nameBase c
                nm   = TH.mkName $ 's' : bnm
                def  = TH.FunD nm [TH.Clause [] (TH.NormalB body) []]
                body = TH.AppE (TH.VarE 'literal) (TH.ConE c)
                sig  = TH.SigD nm sType

    let btname = TH.nameBase typeName
        tname  = TH.mkName ('S' : btname)
        tdecl  = TH.TySynD tname [] sType

    pure $ derives ++ [tdecl]

mkDType :: String -> TH.Name -> TH.Q [TH.Dec]
mkDType s n = do
  let
    t = TH.conT n
    sname = TH.mkName $ "S__" ++ s
    dDecl = TH.DataD [] sname [] Nothing [] []

  xDecl <- mkSort sname

  iDecl <- [d|instance SingleVal $(TH.conT sname)
              instance Avs $(t) where
                type Rep $(t) = SBV $(TH.conT sname)
              instance Ava $(t) where
                type Sv $(t) = $(TH.conT sname)
           |]

  return $ [dDecl] ++ xDecl ++ iDecl
