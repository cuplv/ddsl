{-# LANGUAGE FlexibleContexts #-}

module Ddsl.Ext.ForallCheck
  ( checkForall
  , universal
  , checkExists
  ) where

import Ddsl
import Ddsl.Atom
import Ddsl.Symbolic
import Ddsl.Term

import Data.SBV

data ForallCheck a e
  = ForallCheck
    { faProgram :: Alp (a,e) Bool
    , faSymbol :: MVFun (Rep a) SBool
    , faName :: String
    }

faTheory :: (Avs a, Avs e, QE a e) => ForallCheck a e -> Theory
faTheory f = rule ("FA__" ++ faName f) $ do
  let forAll = applyMV mvw (faSymbol f)

  axiom $ \(a,e) ->
    forAll a .=> alpFlat (faProgram f) (a,e)

  axiom $ \a ->
    sNot (forAll a)
    .=> (existsA $ \e ->
            sNot (alpFlat (faProgram f) (a,e)))

mkForallCheck
  :: (Avs a, Avs e, SMTDefinable (MVFun (Rep a) SBool))
  => String
  -> Alp (a,e) Bool
  -> ForallCheck a e
mkForallCheck = mkForallCheck' undefined

mvwFa :: (Avs a) => a -> Mvw (Rep a) SBool
mvwFa _ = mvw

mkForallCheck'
  :: (Avs a, Avs e, SMTDefinable (MVFun (Rep a) SBool))
  => a
  -> String
  -> Alp (a,e) Bool
  -> ForallCheck a e
mkForallCheck' wa n p = ForallCheck
  { faProgram = p
  , faSymbol = s
  , faName = n
  }
  where
    sname = "FA__" ++ n
    s = mkMVFun (mvwFa wa) $ applyMV mvw (uninterpret sname)

checkForall'
  :: (Avs x, Avs a, Avs e, QE a e)
  => ForallCheck a e
  -> Alp x a
  -> Alp x Bool
checkForall' f = eform $ atomFunTh
  (faTheory f)
  (faSymbol f)
  (error "checkForall is SMT-only.")

checkForall
  :: (Avs x, Avs a, Avs e, QE a e, SMTDefinable (MVFun (Rep a) SBool))
  => String
  -> Alp (a,e) Bool
  -> Alp x a
  -> Alp x Bool
checkForall n p a = checkForall' (mkForallCheck n p) a

universal
  :: (Avs x, Avs a, Avs e, QE a e, SMTDefinable (MVFun (Rep a) SBool))
  => String
  -> Alp x a
  -> (Alp (a,e) a -> Alp (a,e) e -> Alp (a,e) Bool)
  -> Alp x Bool
universal n a p = checkForall n (p tup2g1 tup2g2) a

checkExists
  :: (Avs x, Avs a, Avs e, QE a e, SMTDefinable (MVFun (Rep a) SBool))
  => String
  -> Alp (a,e) Bool
  -> Alp x a
  -> Alp x Bool
checkExists n p a = notE $ checkForall n p a
