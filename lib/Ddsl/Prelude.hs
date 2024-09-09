{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Ddsl.Prelude
  ( module Ddsl
  , module Ddsl.Ext.Accum
  , module Ddsl.Ext.Map
  , module Ddsl.Ext.Nat
  , module Ddsl.Ext.Set
  , module Ddsl.Ext.CardSet
  , module Ddsl.Ext.ForallCheck
  , defaultConfig
  , Bool
  , ($)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (==>)
  , not
  , filterMap
  , nonePassMap
  , filterSet
  , nonePassSet
  , IO
  , Dv
  , Df
  , Df2
  , Df3
  , Df4
  , Df5
  , Df6
  , Df7
  , Df8
  , Show (..)
  , Eq (..)
  , Ord (..)
  , Int
  -- , untup2
  -- , untup3
  -- , untup4
  -- , untup5
  , tup3m1
  , tup3m2
  , tup3m3
  -- , tup4m1
  -- , tup4m2
  , tup4m2
  , tup4m3
  , tup4m4
  -- , tup4m4
  -- , tup5m1
  -- , tup5m2
  -- , tup5m3
  -- , tup5m4
  -- , tup5m5
  , (>)
  , (>=)
  , ite
  ) where

import Ddsl
import Ddsl.Ext.Accum
import Ddsl.Ext.Map hiding (filterMap,nonePassMap)
import Ddsl.Ext.Nat
import Ddsl.Ext.Set hiding (filterSet,nonePassSet)
import Ddsl.Ext.CardSet
import Ddsl.Ext.ForallCheck

import Data.SBV (SMTDefinable,SBool)
import Prelude hiding ((==),(/=),(&&),(||),not,(>),(>=))

not :: (Avs x) => Alp x Bool -> Alp x Bool
not = notE

(==) :: (Avs x, Avs a, Eq a) => Alp x a -> Alp x a -> Alp x Bool
(==) = ($==)

(/=) :: (Avs x, Avs a, Eq a) => Alp x a -> Alp x a -> Alp x Bool
(/=) = ($/=)

(&&) :: (Avs a) => Alp a Bool -> Alp a Bool -> Alp a Bool
(&&) = ($/\)

(||) :: (Avs a) => Alp a Bool -> Alp a Bool -> Alp a Bool
(||) = ($\/)

(==>) :: (Avs a) => Alp a Bool -> Alp a Bool -> Alp a Bool
(==>) = ($=>)

filterMap
  :: (Avs x, Avs a, MapMd k v, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))
  => String
  -> Alp x a
  -> Alp x (Map k v)
  -> (Alp (a,k,v) a -> Alp (a,k,v) k -> Alp (a,k,v) v -> Alp (a,k,v) Bool)
  -> Alp x (Map k v)
filterMap name args m f = filterMapE name f args m

nonePassMap
  :: (Avs x, Avs a, MapMd k v, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Map k v)) (MVFun (Rep (Map k v)) SBool))))
  => String
  -> Alp x a
  -> Alp x (Map k v)
  -> (Alp (a,k,v) a -> Alp (a,k,v) k -> Alp (a,k,v) v -> Alp (a,k,v) Bool)
  -> Alp x Bool
nonePassMap name args m f = isEmptyMap $ filterMap name args m f

filterSet
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp x a
  -> Alp x (Set e)
  -> (Alp (a,e) a -> Alp (a,e) e -> Alp (a,e) Bool)
  -> Alp x (Set e)
filterSet name args s f = filterSetE name f args s

nonePassSet
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp x a
  -> Alp x (Set e)
  -> (Alp (a,e) a -> Alp (a,e) e -> Alp (a,e) Bool)
  -> Alp x Bool
nonePassSet name args s f = isEmptySet $ filterSet name args s f

type Dv a = forall x. (Avs x) => Alp x a

type Df a b = forall x. (Avs x) => Alp x a -> Alp x b

type Df2 a b c = forall x. (Avs x) => Alp x a -> Alp x b -> Alp x c

type Df3 a b c d = forall x. (Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d

type Df4 a b c d e = forall x. (Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e

type Df5 a b c d e f = forall x. (Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e -> Alp x f

type Df6 a b c d e f g = forall x. (Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e -> Alp x f -> Alp x g

type Df7 a b c d e f g h = forall x. (Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e -> Alp x f -> Alp x g -> Alp x h

type Df8 a b c d e f g h i = forall x. (Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e -> Alp x f -> Alp x g -> Alp x h -> Alp x i

defaultConfig :: SolverConfig
defaultConfig = mempty

-- untup2 :: (Avs a, Avs b, Avs x) => Dv (a,b) -> Df2 a b x -> Dv x
-- untup2 = from2'

-- untup3 :: (Avs a, Avs b, Avs c, Avs x) => Dv (a,b,c) -> Df3 a b c x -> Dv x
-- untup3 = from3'

-- untup4 :: (Avs a, Avs b, Avs c, Avs d, Avs x) => Dv (a,b,c,d) -> Df4 a b c d x -> Dv x
-- untup4 = from4'

-- untup5 :: (Avs a, Avs b, Avs c, Avs d, Avs e, Avs x) => Dv (a,b,c,d,e) -> Df5 a b c d e x -> Dv x
-- untup5 = from5'

tup3m1 :: (Avs x1, Avs x2, Avs b, Avs c, Avs z) => Alp z (x1,b,c) -> (Alp z x1 -> Alp z x2) -> Alp z (x2,b,c)
tup3m1 t f =
  from3' t $ \x b c ->
  tup3 (f x) b c

tup3m2 :: (Avs x1, Avs x2, Avs a, Avs c, Avs z) => Alp z (a,x1,c) -> (Alp z x1 -> Alp z x2) -> Alp z (a,x2,c)
tup3m2 t f =
  from3' t $ \a x c ->
  tup3 a (f x) c

tup3m3 :: (Avs x1, Avs x2, Avs a, Avs b, Avs z) => Alp z (a,b,x1) -> (Alp z x1 -> Alp z x2) -> Alp z (a,b,x2)
tup3m3 t f =
  from3' t $ \a b x ->
  tup3 a b (f x)

-- tup4m1 :: (Avs x1, Avs x2, Avs b, Avs c, Avs d) => Dv (x1,b,c,d) -> Df x1 x2 -> Dv (x2,b,c,d)
-- tup4m1 t f =
--   untup4 t $ \x b c d ->
--   tup4 (f x) b c d

tup4m2 :: (Avs x1, Avs x2, Avs a, Avs c, Avs d, Avs z) => Alp z (a,x1,c,d) -> (Alp z x1 -> Alp z x2) -> Alp z (a,x2,c,d)
tup4m2 t f =
  from4' t $ \a x c d ->
  tup4 a (f x) c d

tup4m3 :: (Avs x1, Avs x2, Avs a, Avs b, Avs d, Avs z) => Alp z (a,b,x1,d) -> (Alp z x1 -> Alp z x2) -> Alp z (a,b,x2,d)
tup4m3 t f =
  from4' t $ \a b x d ->
  tup4 a b (f x) d

tup4m4 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs z) => Alp z (a,b,c,x1) -> (Alp z x1 -> Alp z x2) -> Alp z (a,b,c,x2)
tup4m4 t f =
  from4' t $ \a b c x ->
  tup4 a b c (f x)

-- tup4m4 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c) => Dv (a,b,c,x1) -> Df x1 x2 -> Dv (a,b,c,x2)
-- tup4m4 t f =
--   untup4 t $ \a b c x ->
--   tup4 a b c (f x)

-- tup5m1 :: (Avs x1, Avs x2, Avs b, Avs c, Avs d, Avs e) => Dv (x1,b,c,d,e) -> Df x1 x2 -> Dv (x2,b,c,d,e)
-- tup5m1 t f =
--   untup5 t $ \x b c d e ->
--   tup5 (f x) b c d e

-- tup5m2 :: (Avs x1, Avs x2, Avs a, Avs c, Avs d, Avs e) => Dv (a,x1,c,d,e) -> Df x1 x2 -> Dv (a,x2,c,d,e)
-- tup5m2 t f =
--   untup5 t $ \a x c d e ->
--   tup5 a (f x) c d e

-- tup5m3 :: (Avs x1, Avs x2, Avs a, Avs b, Avs d, Avs e) => Dv (a,b,x1,d,e) -> Df x1 x2 -> Dv (a,b,x2,d,e)
-- tup5m3 t f =
--   untup5 t $ \a b x d e ->
--   tup5 a b (f x) d e

-- tup5m4 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs e) => Dv (a,b,c,x1,e) -> Df x1 x2 -> Dv (a,b,c,x2,e)
-- tup5m4 t f =
--   untup5 t $ \a b c x e ->
--   tup5 a b c (f x) e

-- tup5m5 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs d) => Dv (a,b,c,d,x1) -> Df x1 x2 -> Dv (a,b,c,d,x2)
-- tup5m5 t f =
--   untup5 t $ \a b c d x ->
--   tup5 a b c d (f x)

(>) :: (NatMd a, Avs x) => Alp x a -> Alp x a -> Alp x Bool
(>) a b = a $> b

(>=) :: (NatMd a, Avs x) => Alp x a -> Alp x a -> Alp x Bool
(>=) a b = a $>= b

-- ite :: (Avs a) => Dv Bool -> Dv a -> Dv a -> Dv a
ite :: (Avs a, Avs x) => Alp x Bool -> Alp x a -> Alp x a -> Alp x a
ite = iteE
