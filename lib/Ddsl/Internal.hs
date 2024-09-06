{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Ddsl.Internal where

import Ddsl.Symbolic

import Data.SBV
import Data.SBV.Control
import Data.SBV.Either
import Data.SBV.Maybe
import Data.SBV.Tuple
import qualified Data.SBV.Either as SE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Time.Clock
import Data.Time.Format

data RuleId = RuleId { ruleId :: String } deriving (Show,Eq,Ord)

type Theory = Map RuleId (Symbolic ())

rule :: String -> Symbolic () -> Theory
rule i c = Map.singleton (RuleId i) c

rule' :: Theory -> String -> Symbolic () -> Theory
rule' h i c = h <> rule i c

emptyTh :: Theory
emptyTh = Map.empty

applyTheory :: Theory -> Symbolic ()
applyTheory = Map.foldr (>>) (return ())

data Atom a b where
  Atom :: (Avs a, Avs b) => MVFun (Rep (a,b)) SBool -> (a -> b) -> Atom a b
  FunAtom :: (Avs a, Avs b) => MVFun (Rep a) (Rep b) -> (a -> b) -> Atom a b
  PredAtom :: (Avs a, Avs b) => MVFun (Rep b) SBool -> b -> Atom a b
  WrapAtom :: (Avs a, Avs b) => Alp a b -> (a -> b) -> Atom a b

data Alp a b where
  AlpId :: (Avs a) => Alp a a
  AlpBind :: (Avs x, Avs a, Avs b) => (Alp x a -> Alp x b) -> Alp (x,a) b
  AlpAtom :: (Avs a, Avs b) => Theory -> Atom a b -> Alp a b
  AlpSeq :: (Avs a, Avs b, Avs c) => Alp a b -> Alp b c -> Alp a c
  AlpOn1 :: (Avs a1, Avs a2, Avs b1) => Alp a1 b1 -> Alp (a1,a2) (b1,a2)
  AlpOn2 :: (Avs a1, Avs a2, Avs b2) => Alp a2 b2 -> Alp (a1,a2) (a1,b2)

alpFlat :: (Avs a, Avs b) => Alp a b -> Rep a -> Rep b
alpFlat m a = case m of
  AlpId -> a
  AlpBind f ->
    let v = atomConst (snd a) undefined
    in alpFlat (f v) (fst a)
  AlpAtom _ (Atom _ _) -> error "Can't alpFlat relation atoms."
  AlpAtom _ (PredAtom _ _) -> error "Can't alpFlat predicate atoms."
  AlpAtom _ (FunAtom r _) -> applyMV mvw r a
  AlpAtom _ (WrapAtom m1 _) -> alpFlat m1 a
  AlpSeq m1 m2 -> alpFlat m2 (alpFlat m1 a)
  AlpOn1 m1 -> (alpFlat m1 (fst a), snd a)
  AlpOn2 m2 -> (fst a, alpFlat m2 (snd a))

alpSymbol :: (Avs a, Avs b) => Alp a b -> Rep a -> Symbolic (Rep b)
alpSymbol m a = case m of
  AlpId -> return a
  AlpBind f ->
    let v = atomConst (snd a) undefined
    in alpSymbol (f v) (fst a)
  AlpAtom _ (Atom r _) -> do
    b <- quantifyMV
    constrain (applyMV mvw r (a,b) :: SBool)
    return b
  AlpAtom _ (PredAtom r _) -> do
    b <- quantifyMV
    constrain (applyMV mvw r b :: SBool)
    return b
  AlpAtom _ (FunAtom r _) -> return $ applyMV mvw r a
  AlpAtom _ (WrapAtom m1 _) -> alpSymbol m1 a
  AlpSeq m1 m2 -> alpSymbol m1 a >>= alpSymbol m2
  AlpOn1 m1 -> do
    b1 <- alpSymbol m1 (fst a)
    return (b1, snd a)
  AlpOn2 m2 -> do
    b2 <- alpSymbol m2 (snd a)
    return (fst a, b2)

alpFun :: (Avs a, Avs b) => Alp a b -> (a -> b)
alpFun = \case
  AlpId -> id
  AlpBind f -> \a ->
    let v = atomConst undefined (snd a)
    in alpFun (f v) (fst a)
  AlpAtom _ (Atom _ f) -> f
  AlpAtom _ (PredAtom _ b) -> const b
  AlpAtom _ (FunAtom _ f) -> f
  AlpAtom _ (WrapAtom _ f) -> f
  AlpSeq m1 m2 -> alpFun m2 . alpFun m1
  AlpOn1 m1 -> \(a1,a2) -> (alpFun m1 a1, a2)
  AlpOn2 m2 -> \(a1,a2) -> (a1, alpFun m2 a2)

alpTheory :: (Avs a, Avs b) => Alp a b -> Theory
alpTheory = \case
  AlpId -> emptyTh
  AlpBind f ->
    let v = atomFun undefined undefined
    in alpTheory (f v)
  AlpAtom h a -> h <> atomTheory a
  AlpSeq m1 m2 -> alpTheory m1 <> alpTheory m2
  AlpOn1 m1 -> alpTheory m1
  AlpOn2 m2 -> alpTheory m2

atomTheory :: (Avs a, Avs b) => Atom a b -> Theory
atomTheory = \case
  WrapAtom m _ -> alpTheory m
  _ -> emptyTh

-- arrC :: (Avs a, Avs b) => Sy b -> b -> Alp a b
-- arrC = atomConst

atomFun :: (Avs a, Avs b) => MVFun (Rep a) (Rep b) -> (a -> b) -> Alp a b
atomFun = atomFunTh emptyTh

atomFunTh :: (Avs a, Avs b) => Theory -> MVFun (Rep a) (Rep b) -> (a -> b) -> Alp a b
atomFunTh h sf f = AlpAtom h (FunAtom sf f)

atomRel :: (Avs a, Avs b) => MVFun (Rep (a,b)) SBool -> (a -> b) -> Alp a b
atomRel = atomRelTh emptyTh

atomRelTh :: (Avs a, Avs b) => Theory -> MVFun (Rep (a,b)) SBool -> (a -> b) -> Alp a b
atomRelTh h r f = AlpAtom h (Atom r f)

atomPred :: (Avs a, Avs b) => (MVFun (Rep b) SBool) -> b -> Alp a b
atomPred = atomPredTh emptyTh

atomPredTh :: (Avs a, Avs b) => Theory -> MVFun (Rep b) SBool -> b -> Alp a b
atomPredTh h p v = AlpAtom h (PredAtom p v)

atomConst :: (Avs a, Avs b) => Rep b -> b -> Alp a b
atomConst = atomConstTh emptyTh

atomConstTh :: (Avs a, Avs b) => Theory -> Rep b -> b -> Alp a b
atomConstTh h a v = atomPredTh h (mkMVFun mvw $ eqMV a) v

atomWrapped :: (Avs a, Avs b) => Alp a b -> (a -> b) -> Alp a b
atomWrapped m f = AlpAtom emptyTh (WrapAtom m f)

-- mkConst :: (Avs a, Avs b) => (Sy b -> SBool) -> b -> Alp a b
-- mkConst = atomPred

mkBind :: (Avs a, Avs b, Avs c) => (Alp a b -> Alp a c) -> Alp (a,b) c
mkBind = AlpBind

mkSeqLR :: (Avs a, Avs b, Avs c) => Alp a b -> Alp b c -> Alp a c
mkSeqLR = AlpSeq

($>>) :: (Avs a, Avs b, Avs c) => Alp a b -> Alp b c -> Alp a c
($>>) = mkSeqLR

mkDup :: (Avs a) => Mvw (Rep a) (Rep (a,a)) -> Alp a (a,a)
mkDup w = atomFun
  (mkMVFun w $ \a -> (a,a))
  (\a -> (a,a))

dup2 :: (Avs a) => Alp a (a,a)
dup2 = mkDup mvw

-- dup3 :: (Avs a) => Alp a (a,a,a)
-- dup3 = atomFun
--   (mkMVFun $ \a -> (a,(a,a)))
--   (\a -> (a,a,a))

-- dup4 :: (Avs a) => Alp a (a,a,a,a)
-- dup4 = atomFun
--   (mkMVFun $ \a -> (a,(a,(a,a))))
--   (\a -> (a,a,a,a))

-- mkFlip :: (Avs a, Avs b) => Alp (a,b) (b,a)
-- mkFlip = atomFun (\a -> tuple (_2 a, _1 a)) (\(a,b) -> (b,a))

-- -- mkFlop :: (Avs a, Avs b) => Alp (Either a b) (Either b a)
-- -- mkFlop = atomFun
-- --   (SE.either SE.sRight SE.sLeft)
-- --   (\case
-- --       Left a -> Right a
-- --       Right b -> Left b)

-- t21Wit :: (MultiVal a, MultiVal b) => Mvw (a,b) a
-- t21Wit = mvw

-- data AWit a b

-- mkAWit :: AWit a b
-- mkAWit = undefined

tup2g1' :: (Avs a, Avs b) => Mvw (Rep (a,b)) (Rep a) -> Alp (a,b) a
tup2g1' w =
  -- let w :: Mvw (a,b) a
  --     w = mvw
  atomFun (mkMVFun w $ \(a,b) -> a) fst

tup2g1 :: (Avs a, Avs b) => Alp (a,b) a
tup2g1 = tup2g1' mvw

tup2g2' :: (Avs a, Avs b) => Mvw (Rep (a,b)) (Rep b) -> Alp (a,b) b
tup2g2' w = atomFun (mkMVFun w $ \(a,b) -> b) snd

tup2g2 :: (Avs a, Avs b) => Alp (a,b) b
tup2g2 = tup2g2' mvw

-- assocR :: (Avs a, Avs b, Avs c) => Alp ((a,b),c) (a,(b,c))
-- assocR = atomFun
--   (\x -> tuple (_1 . _1 $ x, tuple (_2 . _1 $ x, _2 x)))
--   (\((a,b),c) -> (a,(b,c)))

-- assocL :: (Avs a, Avs b, Avs c) => Alp (a,(b,c)) ((a,b),c)
-- assocL = atomFun
--   (\x -> tuple (tuple (_1 x, _1 . _2 $ x), _2 . _2 $ x))
--   (\(a,(b,c)) -> ((a,b),c))

mkOn1 :: (Avs a1, Avs a2, Avs b1) => Alp a1 b1 -> Alp (a1,a2) (b1,a2)
mkOn1 = AlpOn1

tup2o1 :: (Avs a1, Avs a2, Avs b1) => Alp a1 b1 -> Alp (a1,a2) (b1,a2)
tup2o1 = mkOn1

mkOn2 :: (Avs a1, Avs a2, Avs b2) => Alp a2 b2 -> Alp (a1,a2) (a1,b2)
mkOn2 = AlpOn2

tup2o2 :: (Avs a1, Avs a2, Avs b2) => Alp a2 b2 -> Alp (a1,a2) (a1,b2)
tup2o2 = mkOn2

-- dSumTup
--   :: (Avs a, Avs b, Avs c)
--   => Alp (Either (a,b) c) (Either a c, Either b c)
-- dSumTup = atomFun
--   (SE.either
--     (\x -> tuple (sLeft (_1 x), sLeft (_2 x)))
--     (\x -> tuple (sRight x, sRight x)))
--   (\case
--       Left (a,b) -> (Left a, Left b)
--       Right c -> (Right c, Right c))

-- udSumTup
--   :: (Avs a, Avs b, Avs c)
--   => Alp (Either a c, Either b c) (Either (a,b) c)
-- udSumTup = atomFun
--   (\x -> ite
--     (SE.isLeft (_1 x) .&& SE.isLeft (_2 x))
--     (SE.sLeft $ tuple (SE.fromLeft (_1 x), SE.fromLeft (_2 x)))
--     (SE.either
--       (\_ -> sRight $ fromRight (_2 x))
--       sRight
--       (_1 x)))
--   (\case
--       (Left a, Left b) -> Left (a,b)
--       (Right c, _) -> Right c
--       (_, Right c) -> Right c)

-- mkOnLeft :: (Avs a, Avs b, Avs x) => Alp a b -> Alp (Either a x) (Either b x)
-- mkOnLeft = undefined

-- mkOnRight :: (Avs a, Avs b, Avs x) => Alp a b -> Alp (Either x a) (Either x b)
-- mkOnRight = undefined

alpAssert :: (Avs a) => Alp a Bool -> Symbolic ()
-- alpAssert m = constrain $ \(Forall a) -> alpFlat m a
alpAssert m = constrain $ forallMV w (mkMVFun w $ \a -> alpFlat m a) id
  where w = mvw

data VerifyResult
  = VerifyResult
    { alpResultVal :: Bool
    , alpResultTime :: NominalDiffTime
    }

instance Semigroup VerifyResult where
  VerifyResult v1 t1 <> VerifyResult v2 t2 = VerifyResult (v1 && v2) (t1 + t2)

instance Monoid VerifyResult where
  mempty = VerifyResult True 0

showResultSeconds :: VerifyResult -> String
showResultSeconds (VerifyResult _ t) = formatTime defaultTimeLocale "%3Ess" t

instance Show VerifyResult where
  show r@(VerifyResult v t) =
    let s = showResultSeconds r
    in if v
         then "Proven (" ++ s ++ ")"
         else "Falsified (" ++ s ++ ")"

data SolverConfig
  = SolverConfig
    { alpcMBQI :: Bool
    , alpcShowTheory :: Bool
    , alpcShowSMT :: Bool
    , useSolver :: Maybe SMTConfig
    }

instance Semigroup SolverConfig where
  SolverConfig c1 c2 c3 c4 <> SolverConfig d1 d2 d3 c5 =
    let s = case (c4,c5) of
          (_,Just s) -> Just s
          (Just s,_) -> Just s
          _ -> Nothing
    in SolverConfig (c1 || d1) (c2 || d2) (c3 || d3) s

instance Monoid SolverConfig where
  mempty = SolverConfig False False False (Just cvc5')

cvc4' = cvc4 { extraArgs = ["--full-saturate-quant","--finite-model-find"] }

useCVC4 = mempty { useSolver = Just cvc4' }

cvc5' = cvc5 { extraArgs = ["--full-saturate-quant","--finite-model-find"] }

useCVC5 = mempty { useSolver = Just cvc5' }

useZ3 = mempty { useSolver = Just z3 }

useMBQI = mempty { alpcMBQI = True }

showTheory = mempty { alpcShowTheory = True }

showSMT = mempty { alpcShowSMT = True }

verify :: (Avs a) => (Alp a a -> Alp a Bool) -> IO VerifyResult
verify f = verifyA (f AlpId)

verifyA :: (Avs a) => Alp a Bool -> IO VerifyResult
verifyA = verifyA' mempty

verify' :: (Avs a) => SolverConfig -> (Alp a a -> Alp a Bool) -> IO VerifyResult
verify' conf f = verifyA' conf (f AlpId)

verifyA' :: (Avs a) => SolverConfig -> Alp a Bool -> IO VerifyResult
verifyA' config program = do
  t0 <- getCurrentTime
  runSMTWith c $ do
    if alpcMBQI config
      then setOption $ OptionKeyword ":smt.mbqi" ["true"]
      else return ()
    let aTheory = alpTheory program
    applyTheory aTheory
    result <- alpSymbol program =<< quantifyMV
    constrain $ sNot result
    query $ do
      if alpcShowTheory config
        then io (mapM_ (\x -> putStrLn $ "[Using] " ++ x)
                  (fmap ruleId . Map.keys $ aTheory))
        else return ()
      checkSat >>= \case
        Unsat -> do
          t1 <- io getCurrentTime
          return $ VerifyResult True (diffUTCTime t1 t0)
        Sat -> do
          t1 <- io getCurrentTime
          -- x <- getModel
          -- io $ print x
          return $ VerifyResult False (diffUTCTime t1 t0)
        _ -> do
          r <- getUnknownReason
          io (print r)
          error "Sover returned unknown"
  where
    c = if alpcShowSMT config
      then baseConfig { verbose = True }
      else baseConfig
    baseConfig = case useSolver config of
      Just s -> s
      Nothing -> defaultSMTCfg

evaluate :: (Avs a, Avs b) => (Alp a a -> Alp a b) -> a -> b
evaluate f = alpFun (f AlpId)
