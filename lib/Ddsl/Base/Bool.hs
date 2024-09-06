module Ddsl.Base.Bool
  ( iteE
  , andAll
  , trueE
  , falseE
  , notE
  , ($/\)
  , ($\/)
  , ($=>)
  , ($==)
  , ($/=)
  , andAllA
  ) where

import Ddsl.Atom
import Ddsl.Base.Tuple
import Ddsl.Symbolic
import Ddsl.Term

import Data.SBV

selectBool' :: (Avs a) => Mvw (Rep (Bool, (a,a))) (Rep a) -> Alp (Bool, (a,a)) a
selectBool' w = atomFun
  (mkMVFun w $ \(cond,(a1,a2)) -> iteMV cond a1 a2)
  (\(cond,(a1,a2)) -> if cond then a1 else a2)

selectBool :: (Avs a) => Alp (Bool, (a,a)) a
selectBool = selectBool' mvw

iteA :: (Avs a, Avs b) => Alp a b -> Alp a b -> Alp (Bool, a) b
iteA m1 m2 =
  tup2o2 dup2
  $>> tup2o2 (tup2o1 m1)
  $>> tup2o2 (tup2o2 m2)
  $>> selectBool

iteE :: (Avs a, Avs x) => Alp x Bool -> Alp x a -> Alp x a -> Alp x a
iteE cond mt mf = (cond &&& input) $>> iteA mt mf

andAll :: (Avs a) => [Alp a Bool] -> Alp a Bool
andAll [] = trueE
andAll (m:ms) = iteE m (andAll ms) falseE

notA :: Alp Bool Bool
notA = atomFun (mkMVFun mvw $ sNot) not

notE :: (Avs a) => Alp a Bool -> Alp a Bool
notE m = m $>> notA

andA :: Alp (Bool,Bool) Bool
andA = atomFun
  (mkMVFun mvw $ uncurry (.&&))
  (uncurry (&&))

orA :: Alp (Bool,Bool) Bool
orA = atomFun
  (mkMVFun mvw $ uncurry (.||))
  (uncurry (||))

($/\) :: (Avs a) => Alp a Bool -> Alp a Bool -> Alp a Bool
($/\) m1 m2 = (m1 &&& m2) $>> andA

($\/) :: (Avs a) => Alp a Bool -> Alp a Bool -> Alp a Bool
($\/) m1 m2 = (m1 &&& m2) $>> orA

($=>) :: (Avs a) => Alp a Bool -> Alp a Bool -> Alp a Bool
($=>) m1 m2 = notE m1 $\/ m2

trueE :: (Avs a) => Alp a Bool
trueE = atomConst sTrue True

falseE :: (Avs a) => Alp a Bool
falseE = atomConst sFalse False

eqA' :: (Avs a, Eq a) => Mvw (Rep (a,a)) (Rep Bool) -> Alp (a,a) Bool
eqA' w = atomFun
  (mkMVFun w $ \(a,b) -> eqMV a b)
  (\(a,b) -> a == b)

eqA :: (Avs a, Eq a) => Alp (a,a) Bool
eqA = eqA' mvw

($==) :: (Avs a, Avs b, Eq b) => Alp a b -> Alp a b -> Alp a Bool
($==) m1 m2 = (m1 &&& m2) $>> eqA

($/=) :: (Avs a, Avs b, Eq b) => Alp a b -> Alp a b -> Alp a Bool
($/=) m1 m2 = notE (m1 $== m2)

andAllA :: (Avs a) => [Alp a Bool] -> Alp a Bool
andAllA [] = trueE
andAllA (m:ms) = (m &&& input) $>> iteA (andAllA ms) falseE
