{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Ddsl.Prelude
  ( module Ddsl
  , module Ddsl.Ext.Accum
  , module Ddsl.Ext.Map
  , module Ddsl.Ext.Nat
  , module Ddsl.Ext.Set
  , module Ddsl.Ext.CardSet
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
  , filterSet
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
  ) where

import Ddsl
import Ddsl.Ext.Accum
import Ddsl.Ext.Map hiding (filterMap)
import Ddsl.Ext.Nat
import Ddsl.Ext.Set hiding (filterSet)
import Ddsl.Ext.CardSet

import Data.SBV (SMTDefinable,SBool)
import Prelude hiding ((==),(/=),(&&),(||),not)

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

filterSet
  :: (Avs x, Avs a, SetMd e, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set e)) (MVFun (Rep (Set e)) SBool))))
  => String
  -> Alp x a
  -> Alp x (Set e)
  -> (Alp (a,e) a -> Alp (a,e) e -> Alp (a,e) Bool)
  -> Alp x (Set e)
filterSet name args s f  = filterSetE name f args s

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
