{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Ddsl.Symbolic where

import Data.Kind (Type)
import Data.SBV
import qualified Data.SBV.Either as SE
import qualified Data.SBV.List as SL
import qualified Data.SBV.Maybe as SM
import Data.SBV.Tuple
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

class (SymVal a) => SingleVal a

class MultiVal a where
  data Mvw a :: Type -> Type
  type MVFun a b :: Type
  quantifyMV :: Symbolic a
  applyMV :: Mvw a b -> MVFun a b -> a -> b
  eqMV :: a -> a -> SBool
  forallMV :: Mvw a b -> MVFun a b -> (b -> SBool) -> SBool
  existsMV :: Mvw a b -> MVFun a b -> (b -> SBool) -> SBool
  mkMVFun :: Mvw a b -> (a -> b) -> MVFun a b
  iteMV :: SBool -> a -> a -> a

mvw :: (MultiVal a) => Mvw a b
mvw = undefined

neqMV a b = sNot (eqMV a b)

instance (SingleVal a) => MultiVal (SBV a) where
  data Mvw (SBV a) b = MvwSingle
  type MVFun (SBV a) x = SBV a -> x
  quantifyMV = free_
  applyMV _ f b = f b
  eqMV = (.==)
  forallMV _ f1 f2 = quantifiedBool $ \(Forall a) -> f2 (f1 a)
  existsMV _ f1 f2 = quantifiedBool $ \(Exists a) -> f2 (f1 a)
  mkMVFun _ = id
  iteMV = ite

instance SingleVal Bool

-- instance MultiVal (SBV Bool) where
--   data MVFun (SBV Bool) x = BoolF (SBV Bool -> x)
--   quantifyMV = free_
--   applyMV (BoolF f) b = f b
--   eqMV = (.==)
--   forallMV (BoolF f1) f2 = quantifiedBool $ \(Forall a) -> f2 (f1 a)
--   existsMV (BoolF f1) f2 = quantifiedBool $ \(Exists a) -> f2 (f1 a)
--   mkMVFun = BoolF
--   iteMV = ite

instance MultiVal () where
  data Mvw () b = T0
  type MVFun () x = x
  quantifyMV = pure ()
  applyMV _ f () = f
  eqMV _ _ = sTrue
  forallMV _ b f = f b
  existsMV _ b f = f b
  mkMVFun _ f = f ()
  iteMV _ _ _ = ()

mvwDup :: (MultiVal a) => Mvw a (a,a)
mvwDup = undefined

mvw1 :: (MultiVal a, MultiVal b) => Mvw (a,b) c -> Mvw a (MVFun b c)
mvw1 = undefined

mvw2 :: (MultiVal a, MultiVal b) => Mvw (a,b) c -> Mvw b c
mvw2 = undefined

instance (MultiVal a, MultiVal b) => MultiVal (a, b) where
  data Mvw (a,b) x = T2
  -- type MVFun (a, b) x = a -> b -> x
  type MVFun (a, b) x = MVFun a (MVFun b x)
  quantifyMV = (,) <$> quantifyMV <*> quantifyMV
  applyMV _ f (a,b) = applyMV mvw (applyMV mvw f a) b
  eqMV (a1,b1) (a2,b2) = eqMV a1 a2 .&& eqMV b1 b2
  -- mkMVFun _ f = \a b -> f (a,b)
  mkMVFun w f = mkMVFun mvw (\a -> mkMVFun mvw (\b -> f (a,b)))
  -- w: Mvw (a,b) c, f1: MVFun (a,b) c, f2: c -> SBool
  forallMV w f1 f2 =
    forallMV -- : Mvw a (MVFun b c) -> MVFun a (MVFun b c) -> (MVFun b c -> SBool) -> SBool
      (mvw1 w) -- Mvw a (MVFun b c)
      (mkMVFun (mvw1 w) $ \a -> mkMVFun mvw $ \b -> applyMV w f1 (a,b)) -- MVFun a (MVFun b c)
      -- (MVFun b c -> SBool)
      (\f' -> forallMV (mvw2 w) (mkMVFun (mvw2 w) (\b -> applyMV mvw f' b)) f2)
  existsMV w f1 f2 =
    existsMV
      (mvw1 w)
      (mkMVFun (mvw1 w) $ \a -> mkMVFun mvw $ \b -> applyMV w f1 (a,b))
      (\f' -> existsMV (mvw2 w) (mkMVFun (mvw2 w) (\b -> applyMV mvw f' b)) f2)
  iteMV cond (a1,b1) (a2,b2) = (iteMV cond a1 a2, iteMV cond b1 b2)

-- instance (MultiVal a, MultiVal b, MultiVal c) => MultiVal (a, b, c) where
--   data MVFun (a, b, c) x = T3F (a -> b -> c -> x)
--   quantifyMV = (,,) <$> quantifyMV <*> quantifyMV <*> quantifyMV
--   applyMV (T3F f) (a,b,c) = f a b c
--   eqMV (a1,b1,c1) (a2,b2,c2) = eqMV a1 a2 .&& eqMV b1 b2 .&& eqMV c1 c2
--   mkMVFun f = T3F $ \a b c -> f (a,b,c)
--   -- forallMV (T3F f1) f2 =
--   --   forallMV
--   --     (mkMVFun f1)
--   --     (\f' -> forallMV (mkMVFun (\b -> f' b)) f2)
--   iteMV cond (a1,b1,c1) (a2,b2,c2) =
--     (iteMV cond a1 a2, iteMV cond b1 b2, iteMV cond c1 c2)

-- instance (MultiVal a, MultiVal b, MultiVal c, MultiVal d) => MultiVal (a, b, c, d) where
--   data MVFun (a, b, c, d) x = T4F (a -> b -> c -> d -> x)
--   quantifyMV = (,,,) <$> quantifyMV <*> quantifyMV <*> quantifyMV <*> quantifyMV
--   applyMV (T4F f) (a,b,c,d) = f a b c d
--   eqMV (a1,b1,c1,d1) (a2,b2,c2,d2) = eqMV a1 a2 .&& eqMV b1 b2 .&& eqMV c1 c2 .&& eqMV d1 d2
--   mkMVFun f = T4F $ \a b c d -> f (a,b,c,d)
--   -- forallMV (T3F f1) f2 =
--   --   forallMV
--   --     (mkMVFun f1)
--   --     (\f' -> forallMV (mkMVFun (\b -> f' b)) f2)
--   iteMV cond (a1,b1,c1,d1) (a2,b2,c2,d2) =
--     (iteMV cond a1 a2, iteMV cond b1 b2, iteMV cond c1 c2, iteMV cond d1 d2)

class (MultiVal (Rep a), Eq a) => Avs a where
  type Rep a

instance Avs () where
  type Rep () = ()

instance (Avs a, Avs b) => Avs (a,b) where
  type Rep (a,b) = (Rep a, Rep b)

instance (Avs a, Avs b, Avs c) => Avs (a,b,c) where
  type Rep (a,b,c) = (Rep a, (Rep b, Rep c))

instance (Avs a, Avs b, Avs c, Avs d) => Avs (a,b,c,d) where
  type Rep (a,b,c,d) = (Rep a, (Rep b, (Rep c, Rep d)))

instance (Avs a, Avs b, Avs c, Avs d, Avs e) => Avs (a,b,c,d,e) where
  type Rep (a,b,c,d,e) = (Rep a, (Rep b, (Rep c, (Rep d, Rep e))))

-- instance (Avs a, Avs b, Avs c, Avs d, Avs e) => Avs (a,b,c,d,e) where
--   type Rep (a,b,c,d,e) = (Rep a, Rep b, Rep c, Rep d, Rep e)

instance Avs Bool where
  type Rep Bool = SBV Bool

-- instance (Avs a) => Avs (Maybe a) where
--   type Rep (Maybe a) = Maybe (Rep a)

-- instance (Avs a, Avs b) => Avs (Either a b) where
--   type Rep (Either a b) = Either (Rep a) (Rep b)

-- data SSpec d a b
--   = SSpec (Sy d -> Sy a -> Symbolic (Sy d, Sy b))

-- type FSpec a b = Sy a -> Symbolic (Sy b)

-- type PSpec a b = Sy a -> Sy b -> SBool

-- su = literal ()

-- eitherM
--   :: (Monad m, SymVal a, SymVal b, SymVal c)
--   => (SBV a -> m (SBV c))
--   -> (SBV b -> m (SBV c))
--   -> SEither a b
--   -> m (SBV c)
-- eitherM ml mr v = do
--   cl <- ml (SE.fromLeft v)
--   cr <- mr (SE.fromRight v)
--   return $ SE.either (const cl) (const cr) v

-- bimapM
--   :: (Monad m, SymVal a1, SymVal a2, SymVal b1, SymVal b2)
--   => (SBV a1 -> m (SBV b1))
--   -> (SBV a2 -> m (SBV b2))
--   -> SEither a1 a2
--   -> m (SEither b1 b2)
-- bimapM ml mr = eitherM (\a -> SE.sLeft <$> ml a) (\a -> SE.sRight <$> mr a)

-- type Binr s = s -> s -> Symbolic SBool

class (Avs a, Rep a ~ SBV (Sv a), SymVal (Sv a)) => Ava a where
  type Sv a

instance Ava Bool where
  type Sv Bool = Bool

axiom :: (MultiVal a) => (a -> SBool) -> Symbolic ()
axiom f = constrain $ forallMV w (mkMVFun w f) id
  where w = mvw

-- axiomE :: (MultiVal a, MultiVal b) => (a -> b -> SBool) -> Symbolic ()
-- axiomE f = constrain $ forallMV mvw (mkMVFun mvw f) (\f1 -> existsMV (mkMVFun f1) id)

forallA f = forallMV w (mkMVFun w f) id
  where w = mvw

existsA f = existsMV w (mkMVFun w f) id
  where w = mvw

-- | Implement @'QE' a b@ to assert that a quantifier-alternation edge
-- is allowed to exist from @a@ to @b@.  Implementing both @'QE' a b@
-- and @'QE' b a@ leads to undecidability.
class QE a b

instance QE (Map k v) k
instance QE (Map k v) v
instance QE (Set e) e
