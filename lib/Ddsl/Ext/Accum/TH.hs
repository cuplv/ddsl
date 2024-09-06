{-# LANGUAGE TemplateHaskell #-}

module Ddsl.Ext.Accum.TH
  ( mkAccumMd
  ) where

import Ddsl
import Ddsl.TH
import Ddsl.Ext.Accum.Class

import Data.SBV (SBV)
import Language.Haskell.TH

{- | Declare a Rail type for an 'Accum'. To use this, you need to
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

   @mkAccumMd \"Int_String\" ''Int ''String@

   to declare a Rail type for @'Accum' 'Int' 'String'@,
   assuming that you have already declared Rail types for 'Int' and
   'String'.
-}
mkAccumMd :: String -> Name -> Name -> Q [Dec]
mkAccumMd s kn vn = do
  let
    ktype = ConT kn
    vtype = ConT vn
    sname = mkName $ "S__Accum__" ++ s
    mtype = AppT (AppT (ConT $ mkName "Accum") ktype) vtype
    dDecl = DataD [] sname [] Nothing [] []

  xDecl <- mkSort sname

  iDecl <- [d|instance SingleVal $(conT sname)
              instance Avs (Accum $(conT kn) $(conT vn)) where
                type Rep (Accum $(conT kn) $(conT vn)) = SBV $(conT sname)
              instance Ava (Accum $(conT kn) $(conT vn)) where
                type Sv (Accum $(conT kn) $(conT vn)) = $(conT sname)
              instance AccumMd $(conT kn) $(conT vn) where
                data AccumWit $(conT kn) $(conT vn)
                accumName _ = s
           |]

  return $ [dDecl] ++ xDecl ++ iDecl
