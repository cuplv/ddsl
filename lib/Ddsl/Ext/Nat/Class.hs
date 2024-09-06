{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Nat.Class
  ( NatMd (natName)
  -- , NatNt (..)
  , NatWit
  , natWit
  , zero
  , isZero
  , lessOrEq
  , lessOrEq'
  , ($<=)
  , lessThan
  , ($<)
  , greaterOrEq
  , ($>=)
  , greaterThan
  , ($>)
  -- * Low-level
  , leNatR
  , isZeroR
  , leNatTheory
  , zeroNatTheory
  , leMvw
  , mvwN3
  , leSumR
  , geSumR
  , leSumTheory
  , geSumTheory
  , leSum
  , geSum
  , ltSum
  , gtSum
  ) where

import Ddsl
import Ddsl.Atom
import Ddsl.Term

import Data.SBV
import Data.SBV.Tuple

mvwN :: (NatMd a) => NatWit a -> Mvw (Rep a) SBool
mvwN _ = mvw

mvwN2 :: (NatMd a) => NatWit a -> Mvw (Rep (a,a)) SBool
mvwN2 _ = mvw

mvwN3 :: (NatMd a) => NatWit a -> Mvw (Rep (a,a,a)) SBool
mvwN3 _ = mvw

class
  ( SingleVal (Sv a)
  , Avs a
  , Ava a
  , Ord a
  , Num a
  , SMTDefinable (Rep a -> Rep a -> MVFun (Rep a) SBool)
  ) => NatMd a where
  data NatWit a
  natName :: NatWit a -> String

  isZeroR :: NatWit a -> MVFun (Rep a) SBool
  isZeroR w = mkMVFun (mvwN w) . ufName "isZero" $ w

  leNatR :: NatWit a -> MVFun (Rep (a,a)) SBool
  leNatR w = mkMVFun (mvwN2 w) . ufName "leNat" $ w

  leSumR :: NatWit a -> MVFun (Rep (a,a,a)) SBool
  leSumR w = mkMVFun
    (mvwN3 w)
    (\(n1,(n2,n3)) ->
       applyMV mvw (applyMV mvw (applyMV mvw (ufName "leSum" w) n1) n2) n3)

  geSumR :: NatWit a -> MVFun (Rep (a,a,a)) SBool
  geSumR w = mkMVFun
    (mvwN3 w)
    (\(n1,(n2,n3)) ->
       applyMV mvw (applyMV mvw (applyMV mvw (ufName "geSum" w) n1) n2) n3)

  -- geSumR :: NatWit a -> MVFun (Rep (a,a,a)) SBool
  -- geSumR w = mkMVFun (mvwN3 w) . ufName "geSum" $ w

-- class (NatMd a, Ord a) => NatNt a where
--   natFromInt :: Int -> a
--   intFromNat :: a -> Int

natWit :: (NatMd a) => NatWit a
natWit = undefined

ufName :: (NatMd a, SMTDefinable f) => String -> NatWit a -> f
ufName name = uninterpret . (\k -> name ++ "_" ++ k) . natName

leMvw :: (NatMd a) => NatWit a -> Mvw (Rep (a,a)) SBool
leMvw _ = mvw

leNatTheory :: (NatMd a) => NatWit a -> Theory
leNatTheory w = rule (natName w ++ "__leNat") $ do
  let le a1 a2 = applyMV (leMvw w) (leNatR w) (a1,a2)

  -- Reflexive le
  axiom $ \a -> le a a

  -- Transitive le
  axiom $ \(a,(b,c)) ->
    (le a b .&& le b c)
    .=> le a c

  -- Anti-symmetric le
  axiom $ \(a,b) ->
    (le a b .&& le b a)
    .=> eqMV a b

  -- Total le
  axiom $ \(a,b) ->
    le a b .|| le b a

zeroNatTheory :: (NatMd a) => NatWit a -> Theory
zeroNatTheory w = rule' (leNatTheory w) (natName w ++ "__zeroNat") $ do
  let le a1 a2 = applyMV (leMvw w) (leNatR w) (a1,a2)
      isZero = applyMV mvw (isZeroR w)

  -- Zero is unique
  axiom $ \(a,b) ->
    (isZero a .&& isZero b)
    .=> eqMV a b

  -- Zero is the smallest value
  axiom $ \(a,b) ->
    isZero a .=> le a b

leSumTheory :: (NatMd a) => NatWit a -> Theory
leSumTheory w = rule (natName w ++ "__leSum") $ do
  let
    le n1 n2 = applyMV (leMvw w) (leNatR w) (n1,n2)
    leSum n1 n2 n3 = applyMV (mvwN3 w) (leSumR w) (n1,(n2,n3))

  axiom $ \(c1,(c2,(c3,(c4,c5)))) ->
    (leSum c1 c2 c3
     .&& le c2 c4
     .&& le c3 c5)
    .=> leSum c1 c4 c5

geSumTheory :: (NatMd a) => NatWit a -> Theory
geSumTheory w = rule (natName w ++ "__geSum") $ do
  let
    le n1 n2 = applyMV (leMvw w) (leNatR w) (n1,n2)
    ge n1 n2 = le n2 n1
    geSum n1 n2 n3 = applyMV (mvwN3 w) (geSumR w) (n1,(n2,n3))

  axiom $ \(c1,(c2,(c3,(c4,c5)))) ->
    (geSum c1 c2 c3
     .&& ge c2 c4
     .&& ge c3 c5)
    .=> geSum c1 c4 c5

  -- -- Seems to be redundant with previous axiom
  -- axiom $ \(c1,(c2,(c3,(c4,c5)))) ->
  --   (sNot (geSum c1 c2 c3)
  --    .&& le c2 c4
  --    .&& le c3 c5)
  --   .=> sNot (geSum c1 c4 c5)

isZero :: (Avs x, NatMd a) => Alp x a -> Alp x Bool
isZero = isZero' natWit

isZero' :: (Avs x, NatMd a) => NatWit a -> Alp x a -> Alp x Bool
isZero' w = eform $ atomFunTh
  (zeroNatTheory w)
  (isZeroR w)
  (== 0)

zero :: (Avs x, NatMd a) => Alp x a
zero = zero' natWit

zero' :: (Avs x, NatMd a) => NatWit a -> Alp x a
zero' w = atomPredTh
  (zeroNatTheory w)
  (isZeroR w)
  (0)

($<=) :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
($<=) = lessOrEq

lessOrEq :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
lessOrEq = lessOrEq' natWit

lessOrEq' :: (Avs x, NatMd a) => NatWit a -> Alp x a -> Alp x a -> Alp x Bool
lessOrEq' w = eform2 $ atomFunTh
  (leNatTheory w)
  (leNatR w)
  (uncurry (<=))

($<) :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
($<) = lessThan

lessThan :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
lessThan a b = notE $ greaterOrEq a b

($>=) :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
($>=) = greaterOrEq

greaterOrEq :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
greaterOrEq a b = lessOrEq b a

($>) :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
($>) = greaterThan

greaterThan :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x Bool
greaterThan a b = notE $ lessOrEq a b

leSum' :: (Avs x, NatMd a) => NatWit a -> Alp x a -> Alp x a -> Alp x a -> Alp x Bool
leSum' w = eform3 $ atomFunTh
  (leSumTheory w)
  (leSumR w)
  (\(a,b,c) -> a <= (b + c))

leSum :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x a -> Alp x Bool
leSum = leSum' natWit

geSum' :: (Avs x, NatMd a) => NatWit a -> Alp x a -> Alp x a -> Alp x a -> Alp x Bool
geSum' w = eform3 $ atomFunTh
  (geSumTheory w)
  (geSumR w)
  (\(a,b,c) -> a >= (b + c))

geSum :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x a -> Alp x Bool
geSum = geSum' natWit

ltSum :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x a -> Alp x Bool
ltSum a b c = leSum a b c $/\ notE (geSum a b c)

gtSum :: (Avs x, NatMd a) => Alp x a -> Alp x a -> Alp x a -> Alp x Bool
gtSum a b c = geSum a b c $/\ notE (leSum a b c)
