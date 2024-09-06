{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Ddsl.Base where

import Ddsl.Base.Tuple
import Ddsl.Symbolic
import Ddsl.Term

import Data.SBV
import Data.SBV.Either
import qualified Data.SBV.Maybe as SM
import Data.SBV.Tuple

-- -- Operators

-- (+++)
--   :: (Avs a, Avs b, Avs c, Avs d)
--   => Alp a b
--   -> Alp c d
--   -> Alp (Either a c) (Either b d)
-- (+++) ml mr =
--   tup2c1 unitE
--   $>> mkEitherBr (idA *** ml) (idA *** mr)
--   $>> tup2g2

-- (|||)
--   :: (Avs a, Avs b, Avs c)
--   => Alp a c
--   -> Alp b c
--   -> Alp (Either a b) c
-- (|||) ml mr = (ml +++ mr) $>> selectA

-- Fundamental

eform3 
  :: (Avs a, Avs b, Avs c, Avs d, Avs e)
  => Alp (b,c,d) e
  -> Alp a b
  -> Alp a c
  -> Alp a d
  -> Alp a e
eform3 m a1 a2 a3 = tup3 a1 a2 a3 $>> m

unEform2
  :: (Avs a, Avs b, Avs c)
  => (Alp (a,b) a -> Alp (a,b) b -> Alp (a,b) c)
  -> Alp (a,b) c
unEform2 f = f tup2g1 tup2g2

-- Either

-- type Bool' = Maybe' ()

-- type Maybe' a = Either () a

-- instance AFunctor Maybe where
--   fmapA = onJust

-- instance AApplicative Maybe where
--   pureA = asJust
--   bothA = (m2eA *** m2eA) $>> bothA $>> e2mA

-- instance AMonad Maybe where
--   bindA f = m2eA $>> (nothingE ||| f)

-- instance (Avs e) => AFunctor (Either e) where
--   fmapA = onRight

-- instance (Avs e) => AApplicative (Either e) where
--   pureA = asRight
--   bothA = distA 
--     -- Either (Either e a, e) (Either e a, b)
--     $>> onLeft getLeft
--     -- Either e (Either e a, b)
--     $>> onRight (flipA $>> distA $>> onLeft tup2g2)
--     -- Either e (Either e (a,b))
--     $>> (asLeft ||| onRight flipA)

-- instance (Avs e) => AMonad (Either e) where
--   bindA f = asLeft ||| f

-- eitherA
--   :: (Avs a, Avs b, Avs la, Avs lb, Avs ra, Avs rb)
--   => Alp (a,la) (b,lb) -- Left case
--   -> Alp (a,ra) (b,rb) -- Right case
--   -> Alp (a, Either la ra) (b, Either lb rb)
-- eitherA = mkEitherBr

-- eitherElim
--   :: (Avs a, Avs la, Avs ra, Avs b)
--   => Alp (a,la) b -- Left case
--   -> Alp (a,ra) b -- Right case
--   -> Alp (a, Either la ra) b
-- eitherElim ml mr =
--   eitherA (ml $>> tup2c2 unitE) (mr $>> tup2c2 unitE)
--   $>> tup2g1

-- eitherPm
--   :: (Avs a, Avs la, Avs ra, Avs b)
--   => Alp a (Either la ra)
--   -> (Alp a la -> Alp a b) -- Left case
--   -> (Alp a ra -> Alp a b) -- Right case
--   -> Alp a b
-- eitherPm fe fl fr =
--   (idA &&& fe)
--   $>> eitherElim (mkBind fl) (mkBind fr)

-- type Sum3 a b c = Either (Either a b) c

-- sumPm3
--   :: (Avs x, Avs a, Avs b, Avs c, Avs d)
--   => Alp x (Sum3 a b c)
--   -> (Alp x a -> Alp x d)
--   -> (Alp x b -> Alp x d)
--   -> (Alp x c -> Alp x d)
--   -> Alp x d
-- sumPm3 x fa fb fc =
--   eitherPm x
--     (\x' -> eitherPm x' fa fb)
--     fc

-- getLeft :: (Avs a, Avs b) => Alp (Either a b, a) a
-- getLeft = flipA $>> distA $>> (tup2g2 ||| tup2g1)

-- getRight :: (Avs a, Avs b) => Alp (Either a b, b) b
-- getRight = flipA $>> distA $>> (tup2g1 ||| tup2g2)

-- asLeft :: (Avs a, Avs b) => Alp a (Either a b)
-- asLeft = arrF sLeft Left

-- asRight :: (Avs a, Avs b) => Alp b (Either a b)
-- asRight = arrF sRight Right

-- onLeft :: (Avs a, Avs b, Avs c) => Alp a b -> Alp (Either a c) (Either b c)
-- onLeft f = f +++ idA

-- onRight :: (Avs a, Avs b, Avs c) => Alp b c -> Alp (Either a b) (Either a c)
-- onRight f = idA +++ f

-- flattenA
--   :: (Avs a, Avs e)
--   => Alp (Either e (Either e a)) (Either e a)
-- flattenA = undefined

-- selectA :: (Avs a) => Alp (Either a a) a
-- selectA = arrF
--   (Data.SBV.Either.either id id)
--   (\m -> case m of
--            Right a -> a
--            Left a -> a)

-- distA :: (Avs a, Avs b, Avs c) => Alp (a, Either b c) (Either (a,b) (a,c)) 
-- distA = arrF f1 f2
--   where f1 a = bimap
--                  (\al -> tuple (_1 a, al))
--                  (\ar -> tuple (_1 a, ar))
--                  (_2 a)

--         f2 (a, Left b) = Left (a,b)
--         f2 (a, Right c) = Right (a,c)

-- undistA :: (Avs a, Avs b, Avs c) => Alp (Either (a,b) (a,c)) (a, Either b c)
-- undistA = (tup2g1 ||| tup2g1) &&& (tup2g2 +++ tup2g2)

-- b2eA :: Alp Bool (Either () ())
-- b2eA = arrF
--   (\a -> ite a (sRight su) (sLeft su))
--   (\a -> if a
--          then Right ()
--          else Left ())

-- e2bA :: (Avs a, Avs b) => Alp (Either a b) Bool
-- e2bA = falseE ||| trueE

-- asJust :: (Avs a) => Alp a (Maybe a)
-- asJust = arrF SM.sJust Just

-- nothingE :: (Avs a, Avs b) => Alp a (Maybe b)
-- nothingE = atomConst SM.sNothing Nothing

-- justE :: (Avs a, Avs b) => Alp a b -> Alp a (Maybe b)
-- justE m = m $>> asJust

-- fromJust :: (Avs a) => Alp (a,Maybe a) a
-- fromJust = maybeA (tup2g2 $>> tup2c2 unitE) idA $>> tup2g1

-- isJustE :: (Avs a, Avs b) => Alp a (Maybe b) -> Alp a Bool
-- isJustE m = m $>> arrF
--   (\a -> SM.isJust a)
--   (\a -> case a of
--            Just _ -> True
--            Nothing -> False)

-- isNothingE :: (Avs a, Avs b) => Alp a (Maybe b) -> Alp a Bool
-- isNothingE m = notE $ isJustE m

-- m2eA :: (Avs a) => Alp (Maybe a) (Either () a)
-- m2eA = arrF
--   (SM.maybe (literal (Left ())) sRight)
--   (\m -> case m of
--            Just a -> Right a
--            Nothing -> Left ())

-- e2mA :: (Avs a, Avs b) => Alp (Either a b) (Maybe b)
-- e2mA = arrF
--   (Data.SBV.Either.either (\_ -> literal Nothing) SM.sJust)
--   (\m -> case m of
--            Left _ -> Nothing
--            Right a -> Just a)

-- maybeA
--   :: (Avs a, Avs b, Avs c, Avs d)
--   => Alp (a,b) (c,d) -- Just case
--   -> Alp a c -- Nothing case
--   -> Alp (a, Maybe b) (c, Maybe d)
-- maybeA = mkMaybeBr

-- maybeElim
--   :: (Avs a, Avs b, Avs c)
--   => Alp (a,b) c -- Just case
--   -> Alp a c -- Nothing case
--   -> Alp (a, Maybe b) c
-- maybeElim mj mn =
--   maybeA (mj $>> tup2c2 unitE) mn
--   $>> tup2g1

-- maybePm
--   :: (Avs a, Avs b, Avs c)
--   => Alp a (Maybe b)
--   -> (Alp a b -> Alp a c) -- Just case
--   -> Alp a c -- Nothing case
--   -> Alp a c
-- maybePm fm fj fn = (idA &&& fm) $>> maybeElim (mkBind fj) fn

-- bindJust
--   :: (Avs a, Avs b, Avs c)
--   => Alp a (Maybe b)
--   -> (Alp a b -> Alp a (Maybe c))
--   -> Alp a (Maybe c)
-- bindJust fm fj = maybePm fm fj nothingE

-- onJust :: (Avs a, Avs b) => Alp a b -> Alp (Maybe a) (Maybe b)
-- onJust f = tup2c1 unitE $>> maybeA (idA *** f) idA $>> tup2g2

-- Monad stack

class AFunctor m where
  fmapA :: (Avs a, Avs b, Avs (m a), Avs (m b))
        => Alp a b -> Alp (m a) (m b)

(<$>>) :: (AFunctor m, Avs a, Avs b, Avs c, Avs (m b), Avs (m c))
       => Alp a (m b) -> Alp b c -> Alp a (m c)
(<$>>) f g = f $>> fmapA g

class (AFunctor m) => AApplicative m where
  pureA :: (Avs a, Avs (m a)) => Alp a (m a)
  bothA :: (Avs a, Avs b, Avs (m a), Avs (m b), Avs (m (a,b)))
        => Alp (m a, m b) (m (a,b))
  liftA2A :: (Avs a, Avs b, Avs c, Avs (m a), Avs (m b), Avs (m c), Avs (m (a,b)))
          => Alp (a,b) c -> Alp (m a, m b) (m c)
  liftA2A f = bothA $>> fmapA f

class (AApplicative m) => AMonad m where
  bindA :: (Avs a, Avs b, Avs (m a), Avs (m b))
        => Alp a (m b) -> Alp (m a) (m b)

(>>=>) :: (AMonad m, Avs a, Avs b, Avs c, Avs (m a), Avs (m b), Avs (m c))
       => Alp a (m b) -> Alp b (m c) -> Alp a (m c)
(>>=>) f g = f $>> bindA g

returnE 
  :: (Avs a, Avs b, Avs (m b), AApplicative m) 
  => Alp a b 
  -> Alp a (m b)
returnE = ($>> pureA)
