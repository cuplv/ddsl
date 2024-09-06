{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.CardSet.Internal where

import Ddsl
import Ddsl.Atom
import Ddsl.Ext.Nat
import Ddsl.Ext.Set.Class
import Ddsl.Term

import Data.SBV
import Data.Set (Set)
import qualified Data.Set as Set

class IsSet s where
  type IsSetElement s
  emptyIsSet :: s

instance IsSet (Set a) where
  type IsSetElement (Set a) = a
  emptyIsSet = Set.empty

-- class (NatMd (Card s), IsSet s) => CardSet s where
--   type Card s

mvwCard :: (CardSetMd i e) => NatWit i -> SetWit e -> Mvw (Rep (Set e)) (Rep i)
mvwCard _ _ = mvw

mvwCommonCard :: (CardSetMd i e) => NatWit i -> SetWit e -> Mvw (Rep (Set e, Set e)) (Rep i)
mvwCommonCard _ _ = mvw

class (NatMd i, SetMd e) => CardSetMd i e where
  cardR :: (NatWit i, SetWit e) -> MVFun (Rep (Set e)) (Rep i)
  cardR (wn,ws) = mkMVFun (mvwCard wn ws) . ufCardSet "card" $ (wn,ws)

  commonCardR :: (NatWit i, SetWit e) -> MVFun (Rep (Set e, Set e)) (Rep i)
  commonCardR (wn,ws) = mkMVFun (mvwCommonCard wn ws) . ufCardSet "commonCard" $ (wn,ws)

ufCardSet :: (CardSetMd i e, SMTDefinable f) => String -> (NatWit i, SetWit e) -> f
ufCardSet name (wn,ws) =
  uninterpret $ name ++ "__" ++ natName wn ++ "_" ++ elementName ws

cardSetTheory :: (CardSetMd i e) => NatWit i -> SetWit e -> Theory
cardSetTheory wn ws = rule' (leSumTheory wn <> geSumTheory wn) ("cardSet__" ++ natName wn ++ "_" ++ elementName ws) $ do
  let
    member e s = applyMV (memberMvw ws) (memberR ws) (e,s)
    card s = applyMV (mvwCard wn ws) (cardR (wn,ws)) s
    commonCard s1 s2 = applyMV (mvwCommonCard wn ws) (commonCardR (wn,ws)) (s1,s2)
    le n1 n2 = applyMV (leMvw wn) (leNatR wn) (n1,n2)
    lt n1 n2 = le n1 n2 .&& sNot (n1 .== n2)
    leSum n1 n2 n3 = applyMV (mvwN3 wn) (leSumR wn) (n1,(n2,n3))
    geSum n1 n2 n3 = applyMV (mvwN3 wn) (geSumR wn) (n1,(n2,n3))
    subset s1 s2 = applyMV (subsetMvw ws) (subsetR ws) (s1,s2)

  axiom $ \(s1,s2) -> subset s1 s2 .=> le (card s1) (card s2)

  axiom $ \(s1,(s2,s3)) ->
    (leSum (card s3) (commonCard s1 s3) (commonCard s2 s3)
    .&& sNot (geSum (card s3) (commonCard s1 s3) (commonCard s2 s3)))
    .=> (existsA $ \e -> member e s1 .&& member e s2 .&& member e s3)

  axiom $ \(s1,s2) ->
    commonCard s1 s2 .== commonCard s2 s1

  axiom $ \(s1,(s2,s3)) ->
    lt (commonCard s1 s3) (commonCard s2 s3)
    .=> (existsA $ \e -> member e s3 .&& member e s2 .&& sNot (member e s1))

card' :: (Avs x, CardSetMd i e) => NatWit i -> SetWit e -> Alp x (Set e) -> Alp x i
card' wn ws = eform $ atomFunTh
  (cardSetTheory wn ws)
  (cardR (wn,ws))
  (\s -> fromIntegral $ Set.size s)

card :: (Avs x, CardSetMd i e) => Alp x (Set e) -> Alp x i
card = card' natWit setWit

commonCard'
  :: (Avs x, CardSetMd i e)
  => NatWit i
  -> SetWit e
  -> Alp x (Set e)
  -> Alp x (Set e)
  -> Alp x i
commonCard' wn ws = eform2 $ atomFunTh
  (cardSetTheory wn ws)
  (commonCardR (wn,ws))
  (\(s1,s2) -> fromIntegral $ Set.size (Set.intersection s1 s2))

commonCard
  :: (Avs x, CardSetMd i e)
  => Alp x (Set e)
  -> Alp x (Set e)
  -> Alp x i
commonCard = commonCard' natWit setWit
