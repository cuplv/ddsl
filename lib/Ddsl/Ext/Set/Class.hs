{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Ext.Set.Class
  ( SetMd (elementName,memberR)
  , mkMemberR
  , SetWit
  , setWit
  , Set
  , emptySet
  , isEmptySet
  , fullSet
  , isFullSet
  , member
  , subset
  , quorum
  , insertSet
  , flatSelectFst
  -- * Low-level
  , emptySetR
  , memberTheory
  , emptySetTheory
  , fullSetTheory
  , subsetTheory
  , quorumTheory
  , setTheory
  , memberMvw
  , subsetMvw
  , subsetR
  ) where

import Ddsl
import Ddsl.Atom
import Ddsl.Term

import Data.SBV
import Data.Set (Set)
import qualified Data.Set as Set

mvwS :: (SetMd a) => SetWit a -> Mvw (Rep (Set a)) SBool
mvwS = undefined

mvwS2 :: (SetMd a) => SetWit a -> Mvw (Rep (Set a, Set a)) SBool
mvwS2 = undefined

mvwMR :: (SetMd a) => SetWit a -> Mvw (Rep (a, Set a)) SBool
mvwMR = undefined

class (SingleVal (Sv (Set a)), Avs a, Ava (Set a), Ord a, SMTDefinable (MVFun (Rep a) (MVFun (Rep (Set a)) SBool))) => SetMd a where
  data SetWit a
  elementName :: SetWit a -> String

  setWit :: SetWit a
  setWit = undefined

  emptySetR :: SetWit a -> MVFun (Rep (Set a)) SBool
  emptySetR w = mkMVFun (mvwS w) . ufName "emptySet" $ w

  fullSetR :: SetWit a -> MVFun (Rep (Set a)) SBool
  fullSetR w = mkMVFun (mvwS w) . ufName "fullSet" $ w

  memberR :: SetWit a -> MVFun (Rep (a, Set a)) SBool
  memberR w = mkMVFun
    (mvwMR w)
    (\(e,s) -> applyMV mvw (applyMV mvw (ufName "member" w) e) s)

  subsetR :: SetWit a -> MVFun (Rep (Set a, Set a)) SBool
  subsetR w = mkMVFun (mvwS2 w) . uncurry . ufName "subset" $ w

  quorumR :: SetWit a -> MVFun (Rep (Set a, Set a)) SBool
  quorumR w = mkMVFun (mvwS2 w) . uncurry . ufName "quorum" $ w

ufName :: (SetMd a, SMTDefinable f) => String -> SetWit a -> f
ufName name = uninterpret . (\k -> name ++ "_" ++ k) . elementName

mkMemberR w = uninterpret ("member_" ++ elementName w)

memberTheory :: (SetMd a) => SetWit a -> Theory
memberTheory w = rule ("member__" ++ elementName w) $ do
  let member e s = applyMV (memberMvw w) (memberR w) (e,s)

  -- Inequality requires the existence of a distinguisher element that
  -- is member of one set but not the other.
  let hasDist s1 s2 = existsA $ \x ->
        member x s1 ./= member x s2

  axiom $ \(s1,s2) -> neqMV s1 s2 .=> hasDist s1 s2

mvwX :: (SetMd a) => SetWit a -> Mvw (Rep (Set a)) SBool
mvwX _ = mvw

emptySetTheory :: (SetMd a) => SetWit a -> Theory
emptySetTheory w = rule' (memberTheory w) ("emptySet__" ++ elementName w) $ do
  let member e s = applyMV (memberMvw w) (memberR w) (e,s)
      emptySet = applyMV (setArgMvw w) (emptySetR w)

  -- -- Definition
  -- axiom $ \s ->
  --   sNot (applyMV mvw (emptySetR w) s)
  --   .<=> (existsA $ \e -> applyMV mvw (memberR w) (e,s))

  -- Non-empty set has a member
  axiom $ \s ->
    emptySet s
    .|| (existsA $ \e -> member e s)

  -- Empty set contains no elements
  --
  -- See version for fullSetTheory for explanation
  axiom $ \(x,s) ->
    emptySet s .=> sNot (member x s)

  -- Unique empty set
  --
  -- This follows from the definition, but I'm including it for the
  -- same reason as the uniqueness axiom in fullSetTheory.
  axiom $ \(s1,s2) ->
    (emptySet s1 .&& emptySet s2)
    .=> eqMV s1 s2

setArgMvw :: (SetMd a) => SetWit a -> Mvw (Rep (Set a)) SBool
setArgMvw _ = mvw

fullSetTheory :: (SetMd a) => SetWit a -> Theory
fullSetTheory w = rule' (memberTheory w) ("fullSet__" ++ elementName w) $ do
  let member e s = applyMV (memberMvw w) (memberR w) (e,s)
      fullSet = applyMV (setArgMvw w) (fullSetR w)

  -- -- Definition
  -- axiom $ \s ->
  --   sNot (applyMV mvw (fullSetR w) s)
  --   .<=> (existsA $ \e -> sNot $ applyMV mvw (memberR w) (e,s))

  -- Non-full set has some non-member
  axiom $ \s ->
    fullSet s
    .|| (existsA $ \e -> sNot $ member e s)

  -- Full set contains all elements
  --
  -- Splitting the definition into these two axioms gives some speedup
  -- to the election example.
  --
  -- Specifically, 0.466s -> 0.298s in an experiment on my laptop.
  axiom $ \(x,s) ->
    fullSet s .=> member x s

  -- Unique full set
  --
  -- This follows from the definition, but it seems to significantly
  -- speed up queries that use fullSet (at least, in the election example).
  axiom $ \(s1,s2) ->
    (fullSet s1 .&& fullSet s2)
    .=> eqMV s1 s2


subsetMvw :: (SetMd a) => SetWit a -> Mvw (Rep (Set a, Set a)) SBool
subsetMvw _ = mvw

subsetTheory :: (SetMd a) => SetWit a -> Theory
subsetTheory w = rule' (memberTheory w) ("subset__" ++ elementName w) $ do
  let member e s = applyMV (memberMvw w) (memberR w) (e,s)
      subset s1 s2 = applyMV (subsetMvw w) (subsetR w) (s1,s2)

  -- -- Definition
  -- axiom $ \(s1,s2) ->
  --   sNot (applyMV mvw (subsetR w) (s1,s2))
  --   .<=> (existsA $ \e ->
  --            applyMV mvw (memberR w) (e,s1)
  --            .&& sNot (applyMV mvw (memberR w) (e,s2)))

  -- Non-subset implies existence of element in left but not right
  axiom $ \(s1,s2) ->
    subset s1 s2
    .|| (existsA $ \e ->
            member e s1
            .&& sNot (member e s2))

  -- Subset implies all member of left are members of right
  --
  -- Definition is split into these two parts according to same logic
  -- as with fullSet.
  axiom $ \(s1,(s2,e)) ->
    sNot (subset s1 s2)
    .|| sNot (member e s1)
    .|| member e s2

  -- -- Reflexive subset
  -- axiom $ \s -> subset s s

  -- -- Transitive subset
  -- axiom $ \(s1,(s2,s3)) ->
  --   (subset s1 s2 .&& subset s2 s3)
  --   .=> subset s1 s3

  -- Anti-symmetric subset
  axiom $ \(s1,s2) ->
    (subset s1 s2 .&& subset s2 s1)
    .=> eqMV s1 s2

  -- -- Subset implies membership in large
  -- axiom $ \(s1,(s2,x)) ->
  --   (applyMV mvw (subsetR w) (s1,s2) .&& applyMV mvw (memberR w) (x,s1))
  --   .=> applyMV mvw (memberR w) (x,s2)

  -- -- Subset implies non-membership in small
  -- axiom $ \(s1,(s2,x)) ->
  --   (applyMV mvw (subsetR w) (s1,s2) .&& sNot (applyMV mvw (memberR w) (x,s2)))
  --   .=> sNot (applyMV mvw (memberR w) (x,s1))

quorumMvw :: (SetMd a) => SetWit a -> Mvw (Rep (Set a, Set a)) SBool
quorumMvw _ = mvw

quorumTheory :: (SetMd a) => SetWit a -> Theory
quorumTheory w = rule' (memberTheory w) ("quorum__" ++ elementName w) $ do
  let member e s = applyMV (memberMvw w) (memberR w) (e,s)
      quorum q s = applyMV (quorumMvw w) (quorumR w) (q,s)

  -- Two quorums must have a common member
  axiom $ \(s,(q1,q2)) ->
    (quorum q1 s
     .&& quorum q2 s)
    .=> (existsA $ \x ->
            member x q1
            .&& member x q2)

  -- Loss of quorum means loss of a member of the target set
  axiom $ \(s,(q1,q2)) ->
    (quorum q1 s
     .&& sNot (quorum q2 s))
    .=> (existsA $ \x ->
            member x q1
            .&& member x s
            .&& sNot (member x q2))

  -- A target set that escapes relation to a quorum must gain a member
  -- that is not in the quorum
  axiom $ \(s1,(s2,q)) ->
    (quorum q s1
     .&& sNot (quorum q s2))
    .=> (existsA $ \x ->
            member x s2
            .&& sNot (member x s1)
            .&& sNot (member x q))

setTheory :: (SetMd a) => SetWit a -> Theory
setTheory w = mconcat
  [memberTheory w
  ,emptySetTheory w
  ,fullSetTheory w
  ,subsetTheory w
  ,quorumTheory w
  ]

isEmptySet :: (Avs x, SetMd a) => Alp x (Set a) -> Alp x Bool
isEmptySet = isEmptySet' setWit

isEmptySet' :: (Avs x, SetMd a) => SetWit a -> Alp x (Set a) -> Alp x Bool
isEmptySet' w = eform $ atomFunTh
  (emptySetTheory w)
  (emptySetR w)
  Set.null

isFullSet :: (Avs x, SetMd a) => Alp x (Set a) -> Alp x Bool
isFullSet = isFullSet' setWit

isFullSet' :: (Avs x, SetMd a) => SetWit a -> Alp x (Set a) -> Alp x Bool
isFullSet' w = eform $ atomFunTh
  (fullSetTheory w)
  (fullSetR w)
  (error "isFullSet has no implementation.")

emptySet :: (Avs x, SetMd a) => Alp x (Set a)
emptySet = emptySet' setWit

emptySet' :: (Avs x, SetMd a) => SetWit a -> Alp x (Set a)
emptySet' w = atomPredTh
  (emptySetTheory w)
  (emptySetR w)
  Set.empty

fullSet :: (Avs x, SetMd a) => Alp x (Set a)
fullSet = fullSet' setWit

fullSet' :: (Avs x, SetMd a) => SetWit a -> Alp x (Set a)
fullSet' w = atomPredTh
  (fullSetTheory w)
  (fullSetR w)
  (error "fullSet has no implementation.")

member :: (Avs x, SetMd a) => Alp x a -> Alp x (Set a) -> Alp x Bool
member = member' setWit

member' :: (Avs x, SetMd a) => SetWit a -> Alp x a -> Alp x (Set a) -> Alp x Bool
member' w = eform2 $ atomFunTh
  (memberTheory w)
  (memberR w)
  (uncurry Set.member)

subset :: (Avs x, SetMd a) => Alp x (Set a) -> Alp x (Set a) -> Alp x Bool
subset = subset' setWit

subset' :: (Avs x, SetMd a) => SetWit a -> Alp x (Set a) -> Alp x (Set a) -> Alp x Bool
subset' w = eform2 $ atomFunTh
  (subsetTheory w)
  (subsetR w)
  (uncurry Set.isSubsetOf)

quorum :: (Avs x, SetMd a) => Alp x (Set a) -> Alp x (Set a) -> Alp x Bool
quorum = quorum' setWit

quorum' :: (Avs x, SetMd a) => SetWit a -> Alp x (Set a) -> Alp x (Set a) -> Alp x Bool
quorum' w = eform2 $ atomFunTh
  (quorumTheory w)
  (quorumR w)
  (\(a,b) -> (Set.size (Set.intersection a b) * 2) > Set.size b)

flatSelectFstMvw :: (Avs a, SetMd (a,b), SetMd b) => SetWit (a,b) -> Mvw (Rep ((a, Set (a,b)), Set b)) SBool
flatSelectFstMvw _ = mvw

flatSelectFstR
  :: (Avs a, SetMd (a,b), SetMd b, SMTDefinable (MVFun (Rep a) (Rep (Set (a,b)) -> Rep (Set b) -> SBool)))
  => SetWit (a,b)
  -> MVFun (Rep ((a, Set (a,b)), Set b)) SBool
flatSelectFstR w = mkMVFun
  (flatSelectFstMvw w)
  (\((a,s1),s2) -> applyMV mvw (applyMV mvw (applyMV mvw (ufName "flatSelectFst" w) a) s1) s2)

fstWit :: (SetMd (a,b), SetMd b) => SetWit (a,b) -> SetWit b
fstWit _ = setWit

flatSelectFstTheory :: (Avs a, SetMd (a,b), SetMd b, SMTDefinable (MVFun (Rep a) (Rep (Set (a,b)) -> Rep (Set b) -> SBool))) => SetWit (a,b) -> Theory
flatSelectFstTheory w = rule' (memberTheory w <> memberTheory (fstWit w)) ("flatSelectFst__" ++ elementName w) $ do
  let flatSelectFst a s1 s2 =
        applyMV (flatSelectFstMvw w) (flatSelectFstR w) ((a,s1),s2)
      member e s = applyMV (memberMvw w) (memberR w) (e,s)
      member1 e s = applyMV (memberMvw (fstWit w)) (memberR (fstWit w)) (e,s)

  -- Unique output
  axiom $ \(a,(s1,(s2,s3))) ->
    (flatSelectFst a s1 s2
     .&& flatSelectFst a s1 s3)
    .=> eqMV s2 s3

  -- Member of output iff member of input, paired with key
  axiom $ \(a,(b,(s1,s2))) ->
    flatSelectFst a s1 s2
    .=> (member (a,b) s1
         .<=> member1 b s2)

flatSelectFst'
  :: (Avs x, Avs a, SetMd (a,b), SetMd b, SMTDefinable (MVFun (Rep a) (Rep (Set (a,b)) -> Rep (Set b) -> SBool)))
  => SetWit (a,b)
  -> Alp x a
  -> Alp x (Set (a,b))
  -> Alp x (Set b)
flatSelectFst' w = eform2 $ atomRelTh
  (flatSelectFstTheory w)
  (flatSelectFstR w)
  -- (mkMVFun mvw $ \((a,b),c) -> applyMV mvw (flatSelectFstR w) (a,(b,c)))
  undefined

flatSelectFst
  :: (Avs x, Avs a, SetMd (a,b), SetMd b, SMTDefinable (MVFun (Rep a) (Rep (Set (a,b)) -> Rep (Set b) -> SBool)))
  => Alp x a
  -> Alp x (Set (a,b))
  -> Alp x (Set b)
flatSelectFst = flatSelectFst' setWit

insertSetR
  :: (SetMd a, SMTDefinable (MVFun (Rep a) (Rep (Set a) -> Rep (Set a) -> SBool))) => SetWit a -> MVFun (Rep ((a, Set a), Set a)) SBool
insertSetR w = mkMVFun
  (insertSetWit w)
  (\((a,s1),s2) -> applyMV mvw (applyMV mvw (applyMV mvw (ufName "insertSet" w) a) s1) s2)

memberMvw :: (SetMd a) => SetWit a -> Mvw (Rep (a, Set a)) SBool
memberMvw _ = mvw

insertSetWit :: (SetMd a) => SetWit a -> Mvw (Rep ((a, Set a), Set a)) SBool
insertSetWit _ = mvw

insertSetTheory :: (Avs a, SetMd a, SMTDefinable (MVFun (Rep a) (Rep (Set a) -> Rep (Set a) -> SBool))) => SetWit a -> Theory
insertSetTheory w = rule' (memberTheory w) ("insertSet__" ++ elementName w) $ do
  let member e s = applyMV (memberMvw w) (memberR w) (e,s)
      insertSet e s1 s2 = applyMV (insertSetWit w) (insertSetR w) ((e,s1),s2)

  -- Unique output
  axiom $ \(a,(s1,(s2,s3))) ->
    (insertSet a s1 s2 .&& insertSet a s1 s3)
    .=> eqMV s2 s3

  -- Inserted element is member of output
  axiom $ \(a,(s1,s2)) ->
    insertSet a s1 s2
    .=> member a s2

  -- Other elements retain membership
  axiom $ \(a,(b,(s1,s2))) ->
    (insertSet a s1 s2
     .&& sNot (eqMV a b))
    .=> (member b s1
         .<=> member b s2)

insertSet'
  :: (Avs x, SetMd a, SMTDefinable (MVFun (Rep a) (Rep (Set a) -> Rep (Set a) -> SBool)))
  => SetWit a
  -> Alp x a
  -> Alp x (Set a)
  -> Alp x (Set a)
insertSet' w = eform2 $ atomRelTh
  (insertSetTheory w)
  (insertSetR w)
  (uncurry Set.insert)

insertSet
  :: (Avs x, SetMd a, SMTDefinable (MVFun (Rep a) (Rep (Set a) -> Rep (Set a) -> SBool)))
  => Alp x a
  -> Alp x (Set a)
  -> Alp x (Set a)
insertSet = insertSet' setWit
