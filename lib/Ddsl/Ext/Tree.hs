{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Tree
  ( KtTreeMd (ktTreeName)
  , KtTreeWit
  , KtKey
  , KtTree
  , emptyKt
  , emptyKt'
  , appendKt
  , checkKt
  , lookupKt
  , lengthKt'
  -- , sameList
  , prefixMatchKt
  , sublistKt
  , ktWit
  ) where

import Ddsl
import Ddsl.Atom
import Ddsl.Ext.List
import Ddsl.Ext.Nat
import Ddsl.Term

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.SBV
import GHC.Generics hiding (Rep)

data KtKey t i
  = KtKey (Maybe (t,i))
  deriving (Show, Eq, Ord, Generic)

data KtTree t i e
  = KtTree (Map (t, i) (e, KtKey t i))
  deriving (Show, Eq, Ord, Generic)

mvwLen :: (KtTreeMd t i e) => KtTreeWit t i e -> Mvw (Rep (KtKey t i)) (Rep i)
mvwLen _ = mvw

mvwApp :: (KtTreeMd t i e) => KtTreeWit t i e -> Mvw (Rep (((t,e), KtKey t i, KtTree t i e), KtTree t i e)) SBool
mvwApp _ = mvw

mvwAppKey :: (KtTreeMd t i e) => KtTreeWit t i e -> Mvw (Rep (((t,e), KtKey t i), KtKey t i)) SBool
mvwAppKey _ = mvw

mvwCheck :: (KtTreeMd t i e) => KtTreeWit t i e -> Mvw (Rep (KtKey t i, KtTree t i e)) SBool
mvwCheck _ = mvw

mvwLookup :: (KtTreeMd t i e) => KtTreeWit t i e -> Mvw (Rep ((KtKey t i, KtTree t i e), List i e)) SBool
mvwLookup _ = mvw

mvwSameList :: (KtTreeMd t i e) => KtTreeWit t i e -> Mvw (Rep ((KtKey t i, KtTree t i e), (KtKey t i, KtTree t i e))) SBool
mvwSameList _ = mvw

mvwPrefixMatchKt :: (KtTreeMd t i e) => KtTreeWit t i e -> Mvw (Rep (i, (KtKey t i, KtTree t i e), (KtKey t i, KtTree t i e))) SBool
mvwPrefixMatchKt _ = mvw

class
    ( SingleVal (Sv (KtTree t i e))
    , SingleVal (Sv (KtKey t i))
    , Ord t
    , Avs t
    , EqSymbolic (Rep t)
    , ListMd i e
    , Ava (KtKey t i)
    , Ava (KtTree t i e)
    , NatMd i
    , SMTDefinable (MVFun (Rep t) (MVFun (Rep e) (SBV (Sv (KtKey t i)) -> SBV (Sv (KtTree t i e)) -> SBV (Sv (KtTree t i e)) -> SBool)))
    , SMTDefinable (Rep (KtKey t i) -> Rep (KtTree t i e) -> MVFun (Rep (List i e)) SBool)
    , SMTDefinable (MVFun (Rep t) (MVFun (Rep e) (Rep (KtKey t i) -> Rep (KtKey t i) -> SBool)))
    ) => KtTreeMd t i e where
  data KtTreeWit t i e
  ktTreeName :: KtTreeWit t i e -> String

  lengthKtR :: KtTreeWit t i e -> MVFun (Rep (KtKey t i)) (Rep i)
  lengthKtR w = mkMVFun (mvwLen w) . ufKt "ktLength" $ w

  appendKtR :: KtTreeWit t i e -> MVFun (Rep (((t,e), KtKey t i, KtTree t i e), KtTree t i e)) SBool
  appendKtR w = mkMVFun
    (mvwApp w)
    (\((e,(k,m1)),m2) ->
       applyMV mvw (applyMV mvw (applyMV mvw (applyMV mvw (ufKt "ktAppend" w) e) k) m1) m2)

  appKeyKtR :: KtTreeWit t i e -> MVFun (Rep (((t,e), KtKey t i), KtKey t i)) SBool
  appKeyKtR w = mkMVFun
    (mvwAppKey w)
    (\((e,k1),k2) ->
       applyMV mvw (applyMV mvw (applyMV mvw (ufKt "ktAppKey" w) e) k1) k2)

  checkKtR :: KtTreeWit t i e -> MVFun (Rep (KtKey t i, KtTree t i e)) SBool
  checkKtR w = mkMVFun
    (mvwCheck w)
    (\(k,m) -> applyMV mvw (applyMV mvw (ufKt "ktCheck" w) k) m)

  lookupKtR :: KtTreeWit t i e -> MVFun (Rep ((KtKey t i, KtTree t i e), List i e)) SBool
  lookupKtR w = mkMVFun
    (mvwLookup w)
    (\((k,m),l) -> applyMV mvw (applyMV mvw (applyMV mvw (ufKt "ktLookup" w) k) m) l)

  sameListR :: KtTreeWit t i e -> MVFun (Rep ((KtKey t i, KtTree t i e), (KtKey t i, KtTree t i e))) SBool
  sameListR w = mkMVFun
    (mvwSameList w)
    (\((k1,m1),(k2,m2)) -> applyMV mvw (applyMV mvw (applyMV mvw (applyMV mvw (ufKt "ktSameList" w) k1) m1) k2) m2)

  prefixMatchKtR :: KtTreeWit t i e -> MVFun (Rep (i, (KtKey t i, KtTree t i e), (KtKey t i, KtTree t i e))) SBool
  prefixMatchKtR w = mkMVFun
    (mvwPrefixMatchKt w)
    (\(i,((k1,m1),(k2,m2))) -> applyMV mvw (applyMV mvw (applyMV mvw (applyMV mvw (applyMV mvw (ufKt "prefixMatchKt" w) i) k1) m1) k2) m2)

ktWit :: (KtTreeMd t i e) => KtTreeWit t i e
ktWit = undefined

ufKt :: (KtTreeMd t i e, SMTDefinable f) => String -> KtTreeWit t i e -> f
ufKt name = uninterpret . (\s -> name ++ "__" ++ s) . ktTreeName

ktListWit :: (KtTreeMd t i e) => KtTreeWit t i e -> ListWit i e
ktListWit w = listWit

ktIndexWit :: (KtTreeMd t i e) => KtTreeWit t i e -> NatWit i
ktIndexWit w = natWit

ktTheory :: (KtTreeMd t i e) => KtTreeWit t i e -> Theory
ktTheory w = rule' (zeroNatTheory (ktIndexWit w) <> leNatTheory (ktIndexWit w)) ("kt__" ++ ktTreeName w) $ do
  let
    -- wl = ktListWit w
    wi = ktIndexWit w
    check k m = applyMV (mvwCheck w) (checkKtR w) (k,m)
    length = applyMV (mvwLen w) (lengthKtR w)
    appKey (t,e) k1 k2 = applyMV (mvwAppKey w) (appKeyKtR w) (((t,e),k1),k2)
    append (t,e) (k,m1) m2 = applyMV (mvwApp w) (appendKtR w) (((t,e),(k,m1)),m2)
    lookup k m l = applyMV (mvwLookup w) (lookupKtR w) ((k,m),l)
    -- listLength = applyMV (mvwListLen wl) (listLengthR wl)
    -- prefixMatch i l1 l2 = applyMV (mvwListMatch wl) (prefixMatchR wl) (i,(l1,l2))
    isZero = applyMV mvw (isZeroR wi)
    le i1 i2 = applyMV (leMvw wi) (leNatR wi) (i1,i2)
    -- sameList (k1,m1) (k2,m2) = applyMV (mvwSameList w) (sameListR w) ((k1,m1),(k2,m2))
    prefixMatchKt i (k1,m1) (k2,m2) = applyMV (mvwPrefixMatchKt w) (prefixMatchKtR w) (i,((k1,m1),(k2,m2)))

  -- axiom $ \k -> eqMV (length k) (length k)

  -- appKey is functional
  axiom $ \(t,(e,(k1,(k2,k3)))) ->
    (appKey (t,e) k1 k2 .&& appKey (t,e) k1 k3)
    .=> eqMV k2 k3

  -- lookup is functional
  axiom $ \(k,(m,(l1,l2))) ->
    (lookup k m l1 .&& lookup k m l2)
    .=> eqMV l1 l2

  -- append is functional
  axiom $ \(e,(m1,(m2,m3))) ->
    (append e m1 m2 .&& append e m1 m3)
    .=> eqMV m2 m3

  -- -- lengths match
  -- axiom $ \(k,(m,l)) ->
  --   (check k m .&& lookup k m l)
  --   .=> eqMV (length k) (listLength l)

  -- appKey always gives a greater key
  axiom $ \(t,(e,(k1,(k2)))) ->
    appKey (t,e) k1 k2
    .=> ((sNot $ eqMV (length k1) (length k2)) .&& le (length k1) (length k2))

  -- append preserves existing check
  axiom $ \(t,(e,(k1,(k2,(m1,m2))))) ->
    (check k1 m1
     .&& check k2 m1
     .&& append (t,e) (k1,m1) m2)
    .=> check k2 m2

  -- append implies new check
  axiom $ \(t,(e,(k1,(k2,(m1,m2))))) ->
    (check k1 m1
     .&& append (t,e) (k1,m1) m2
     .&& appKey (t,e) k1 k2
    )
    .=> check k2 m2

  -- -- append preserves existing lookups
  -- axiom $ \(t,(e,(k1,(k2,(m1,(m2,(l1))))))) ->
  --   (check k1 m1
  --    .&& append (t,e) (k1,m1) m2
  --    .&& lookup k2 m1 l1)
  --   .=> lookup k2 m2 l1

  -- append gives prefixMatchKt
  axiom $ \(t,(e,(k1,(k2,(m1,m2))))) ->
    (check k1 m1
     .&& append (t,e) (k1,m1) m2
     .&& appKey (t,e) k1 k2)
    .=> prefixMatchKt (length k1) (k1,m1) (k2,m2)

  -- prefixMatchKt is reflexive up to lengthKt
  axiom $ \(k,m) ->
    prefixMatchKt (length k) (k,m) (k,m)

  -- prefixMatchKt i is symmetric
  axiom $ \(i,(k1,(k2,(m1,m2)))) ->
    prefixMatchKt i (k1,m1) (k2,m2)
    .=> prefixMatchKt i (k2,m2) (k1,m1)

  -- prefixMatchKt i is transitive
  axiom $ \(i,(k1,(k2,(k3,(m1,(m2,m3)))))) ->
    (prefixMatchKt i (k1,m1) (k2,m2) .&& prefixMatchKt i (k2,m2) (k3,m3))
    .=> prefixMatchKt i (k1,m1) (k3,m3)

  -- prefixMatchKt is ordered
  axiom $ \(i1,(i2,(k1,(k2,(m1,m2))))) ->
    (le i1 i2
     .&& prefixMatchKt i2 (k1,m1) (k2,m2))
    .=> prefixMatchKt i1 (k1,m1) (k2,m2)

  -- prefixMatchKt is always true up to zero
  axiom $ \(i,(k1,(k2,(m1,m2)))) ->
    isZero i .=> prefixMatchKt i (k1,m1) (k2,m2)

  -- -- prefixMatchKt i implies that lookups prefixMatch
  -- axiom $ \(i,(k1,(k2,(m1,(m2,(l1,l2)))))) ->
  --   (check k1 m1
  --    .&& check k2 m2
  --    .&& prefixMatchKt i (k1,m1) (k2,m2)
  --    .&& lookup k1 m1 l1
  --    .&& lookup k2 m2 l2)
  --   .=> prefixMatch i l1 l2

  -- if equivalent in prefixMatch, the same is true after append
  axiom $ \(t,(e,(k1,(k2,(k1',(k2',(m1,(m2,(m1',m2'))))))))) ->
    (check k1 m1
     .&& check k2 m2
     .&& eqMV (length k1) (length k2)
     .&& prefixMatchKt (length k1) (k1,m1) (k2,m2)
     .&& append (t,e) (k1,m1) m1'
     .&& appKey (t,e) k1 k1'
     .&& append (t,e) (k2,m2) m2'
     .&& appKey (t,e) k2 k2')
    .=> (prefixMatchKt (length k1') (k1',m1') (k2',m2')
         .&& eqMV (length k1') (length k2'))

  -- append creates new prefixMatchKt i
  axiom $ \(i,(t,(e,(k1,(k2,(k1',(k2',(m1,(m2,(m1',m2')))))))))) ->
    (check k1 m1
     .&& check k2 m2
     .&& prefixMatchKt i (k1,m1) (k2,m2)
     .&& append (t,e) (k1,m1) m1'
     .&& appKey (t,e) k1 k1'
     .&& append (t,e) (k2,m2) m2'
     .&& appKey (t,e) k2 k2')
    .=> prefixMatchKt i (k1',m1') (k2',m2')

  -- append preserves existing prefixMatchKt
  axiom $ \(i,(t,(e,(k1,(k2,(k3,(m1,(m2,m1')))))))) ->
    (check k1 m1
     .&& check k2 m2
     .&& prefixMatchKt i (k1,m1) (k2,m2)
     .&& append (t,e) (k3,m1) m1')
    .=> prefixMatchKt i (k1,m1') (k2,m2)

  -- prefix-match requires matched length
  axiom $ \(i,(k1,(k2,(m1,m2)))) ->
    prefixMatchKt i (k1,m1) (k2,m2)
    .=> (le i (length k1)
         .&& le i (length k2))

  -- append for different branches is commutative
  axiom $ \(t1,(t2,(k1,(k2,(e1,(e2,(m,(m1,(m2,(m3,m4)))))))))) ->
    (t1 ./= t2
     .&& append (t1,e1) (k1,m) m1
     .&& append (t2,e2) (k2,m1) m2
     .&& append (t2,e2) (k2,m) m3
     .&& append (t1,e1) (k1,m3) m4)
    .=> (m2 .== m4)

emptyKt
  :: (Avs x, KtTreeMd t i e)
  => Alp x (KtKey t i, KtTree t i e)
emptyKt = atomWrapped undefined f
  where
    f _ = (KtKey Nothing, KtTree Map.empty)

emptyKt' :: (KtKey t i, KtTree t i e)
emptyKt' = (KtKey Nothing, KtTree Map.empty)

lengthFromKey :: (NatMd i) => KtKey t i -> i
lengthFromKey (KtKey m) = case m of
  Just (t,i) -> i + 1
  Nothing -> 0

prefixMatchKt'
  :: (Avs x, KtTreeMd t i e)
  => KtTreeWit t i e
  -> Alp x i
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x Bool
prefixMatchKt' w = eform3 $ atomFunTh
  (ktTheory w)
  (prefixMatchKtR w)
  undefined

prefixMatchKt
  :: (Avs x, KtTreeMd t i e)
  => Alp x i
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x Bool
prefixMatchKt = prefixMatchKt' ktWit

sublistKt
  :: (Avs x, KtTreeMd t i e, NatMd i)
  => Alp x (KtKey t i, KtTree t i e)
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x Bool
sublistKt kt1 kt2 =
  let w = ktWit
  in prefixMatchKt' w (lengthKt' w (fstE kt1)) kt1 kt2

sameList'
  :: (Avs x, KtTreeMd t i e)
  => KtTreeWit t i e
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x Bool
sameList' w = eform2 $ atomFunTh
  (ktTheory w)
  (sameListR w)
  undefined

sameList
  :: (Avs x, KtTreeMd t i e)
  => Alp x (KtKey t i, KtTree t i e)
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x Bool
sameList = sameList' ktWit

appendKt'
  :: (Avs x, KtTreeMd t i e)
  => KtTreeWit t i e
  -> Alp x (t,e)
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x (KtTree t i e)
appendKt' w = eform2 $ atomRelTh
  (ktTheory w)
  (appendKtR w)
  undefined

appKeyKt'
  :: (Avs x, KtTreeMd t i e)
  => KtTreeWit t i e
  -> Alp x (t,e)
  -> Alp x (KtKey t i)
  -> Alp x (KtKey t i)
appKeyKt' w = eform2 $ atomRelTh
  (ktTheory w)
  (appKeyKtR w)
  undefined

appendBoth
  :: (KtTreeMd t i e)
  => Alp ((t,e), (KtKey t i, KtTree t i e)) (KtKey t i, KtTree t i e)
appendBoth =
  from2 $ \e m ->
  tup2 (appKeyKt' ktWit e (fstE m)) (appendKt' ktWit e m)

appendKt
  :: (Avs x, KtTreeMd t i e, NatMd i)
  => Alp x (t,e)
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x (KtKey t i, KtTree t i e)
appendKt = eform2 $ atomWrapped appendBoth f
  where
    f ((t,e), (k, KtTree m)) =
      let
        key = (t, lengthFromKey k)
        tree = KtTree $ Map.insert key (e, k) m
      in
        (KtKey . Just $ key, tree)

checkKt'
  :: (Avs x, KtTreeMd t i e)
  => KtTreeWit t i e
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x Bool
checkKt' w = eform $ atomFunTh
  (ktTheory w)
  (checkKtR w)
  (error "Are you sure you want to use checkKt?")

checkKt
  :: (Avs x, KtTreeMd t i e)
  => Alp x (KtKey t i, KtTree t i e)
  -> Alp x Bool
checkKt = checkKt' ktWit

lookupKt'
  :: (Avs x, KtTreeMd t i e)
  => KtTreeWit t i e
  -> Alp x (KtKey t i, KtTree t i e)
  -> Alp x (List i e)
lookupKt' w = eform $ atomRelTh
  (ktTheory w)
  (lookupKtR w)
  (error "Are you sure you want to use lookupKt?")
    -- f (KtKey k, KtTree m) = case k of
    --   Just k -> case Map.lookup k m of
    --     Just (e,next) ->
    --       let
    --         (r, List l') = f (next, KtTree m)
    --       in
    --         (r, List (e : l'))
    --     Nothing -> (False, List [])
    --   Nothing -> (True, List [])

lookupKt
  :: (Avs x, KtTreeMd t i e)
  => Alp x (KtKey t i, KtTree t i e)
  -> Alp x (List i e)
lookupKt = lookupKt' ktWit

lengthKt'
  :: (Avs x, KtTreeMd t i e, NatMd i)
  => KtTreeWit t i e
  -> Alp x (KtKey t i)
  -> Alp x i
lengthKt' w = eform $ atomFunTh
  (ktTheory w)
  (lengthKtR w)
  (\k -> lengthFromKey k)

-- lengthKt
--   :: (Avs x, KtTreeMd t i e)
--   => Alp x (KtKey t i)
--   -> Alp x i
-- lengthKt = lengthKt' ktWit
-- lengthKt = eform $ atomWrapped undefined f
--   where
--     f k = natFromInt $ lengthFromKey k

-- fromListKt
--   :: (Avs x, KtTreeMd t i e)
--   => Alp x t
--   -> Alp x (List i e)
--   -> Alp x (KtKey t i, KtTree t i e)
-- fromListKt = eform2 $ atomWrapped undefined f
--   where
--     f (t, List es) = foldr (\e (k,m) -> appendKt (t,e) (k,m)) emptyKt es
