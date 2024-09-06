module Ddsl.Atom
  ( Alp
  , Theory
  -- , alpTheory
  , rule
  , rule'
  , atomFun
  , atomFunTh
  , atomRel
  , atomRelTh
  , atomPred
  , atomPredTh
  , atomConst
  , atomConstTh
  , atomWrapped
  , tup2g1
  , tup2g2
  -- , mkBind -- ASimulate
  -- , mkDup
  -- , mkSeqLR -- ASequenceLR
  -- , mkTup2 -- ATuple2
  -- , mkBoolBr -- ABool
  -- , mkMaybeBr -- AMaybe
  -- , mkEitherBr -- AEither
  , uncurryS
  ) where

import Ddsl.Internal
import Ddsl.Symbolic

import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.Either as SE
import qualified Data.SBV.Maybe as SM

-- mkSelectMaybe :: (Avs a) => Alp (Maybe a, a) a
-- mkSelectMaybe = atomFun
--   (\x -> SM.maybe (_2 x) id (_1 x))
--   (\(a,d) -> case a of
--       Nothing -> d
--       Just a -> a)

-- mkSelectEither :: (Avs a) => Alp (Either a a) a
-- mkSelectEither = atomFun
--   (SE.either id id)
--   (\a -> case a of
--       Left a -> a
--       Right a -> a)


-- mkMaybeBr
--   :: (Avs a, Avs b, Avs c, Avs d)
--   => Alp (a,b) (c,d) -- Just case
--   -> Alp a c -- Nothing case
--   -> Alp (a, Maybe b) (c, Maybe d)
-- mkMaybeBr = undefined

-- mkEitherDist
--   :: (Avs a, Avs b, Avs c)
--   => Alp (a, Either b c) (Either (a,b) (a,c))
-- mkEitherDist = atomFun
--   (\x -> ite
--     (SE.isLeft (_2 x))
--     (SE.sLeft $ tuple (_1 x, SE.fromLeft (_2 x)))
--     (SE.sRight $ tuple (_1 x, SE.fromRight (_2 x))))
--   (\(a,e) -> case e of
--       Left b -> Left (a,b)
--       Right c -> Right (a,c))

-- mkIntoLeft
--   :: (Avs a, Avs b)
--   => Alp a (Either a b)
-- mkIntoLeft = atomFun
--   SE.sLeft
--   Left

-- mkIntoRight 
--   :: (Avs a, Avs b)
--   => Alp b (Either a b)
-- mkIntoRight = atomFun
--   SE.sRight
--   Right

-- mkEitherUndist
--   :: (Avs a, Avs b, Avs c)
--   => Alp (Either (a,b) (a,c)) (a, Either b c)
-- mkEitherUndist =
--   mkOnLeft (mkOn2 mkIntoLeft)
--   `mkSeqLR` mkOnRight (mkOn2 mkIntoRight)
--   `mkSeqLR` mkSelectEither

-- mkEitherBr
--   :: (Avs a, Avs b, Avs la, Avs lb, Avs ra, Avs rb)
--   => Alp (a,la) (b,lb) -- Left case
--   -> Alp (a,ra) (b,rb) -- Right case
--   -> Alp (a, Either la ra) (b, Either lb rb)
-- mkEitherBr m1 m2 =
--   mkEitherDist
--   -- Either (a, la) (a, ra)
--   `mkSeqLR` mkOnLeft m1
--   `mkSeqLR` mkOnRight m2
--   `mkSeqLR` mkEitherUndist

uncurryS :: (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b -> SBV c) -> SBV (a,b) -> SBV c
uncurryS f x = f (_1 x) (_2 x)
