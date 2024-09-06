module Ddsl.Term
  ( Alp
  , tup2g1
  , tup2g2
  , tup2o1
  , tup2o2
  , tup2
  , dup2
  , ($>>)
  , input
  , eform
  , eform2
  , (&&&)
  , unitE
  , ($>|)
  , ($<<)
  , letb
  , flipA
  , fstE
  , sndE
  ) where

import Ddsl.Internal
import Ddsl.Symbolic

input' :: (Avs a) => Mvw (Rep a) (Rep a) -> Alp a a
input' w = atomFun (mkMVFun w id) id

input :: (Avs a) => Alp a a
input = input' mvw

eform :: (Avs a, Avs b, Avs c) => Alp b c -> Alp a b -> Alp a c
eform = ($<<)

eform2 
  :: (Avs a, Avs b, Avs c, Avs d)
  => Alp (b,c) d
  -> Alp a b
  -> Alp a c
  -> Alp a d
eform2 m a1 a2 = (a1 &&& a2) $>> m

(&&&)
  :: (Avs a, Avs b, Avs x)
  => Alp x a
  -> Alp x b
  -> Alp x (a,b)
(&&&) m1 m2 = dup2 $>> tup2o1 m1 $>> tup2o2 m2

tup2
  :: (Avs a, Avs b, Avs x)
  => Alp x a
  -> Alp x b
  -> Alp x (a,b)
tup2 = (&&&)

unitE' :: (Avs a) => Mvw (Rep a) (Rep ()) -> Alp a ()
unitE' w = atomFun (mkMVFun w . const $ ()) (const ())

unitE :: (Avs a) => Alp a ()
unitE = unitE' mvw

($>|) :: (Avs a, Avs b, Avs c) => Alp a b -> Alp () c -> Alp a c
($>|) t1 t2 = t1 $>> unitE $>> t2

($<<) :: (Avs a, Avs b, Avs c) => Alp b c -> Alp a b -> Alp a c
($<<) = flip ($>>)

passThru :: (Avs a, Avs b) => Alp a b -> Alp a a
passThru f = (input &&& f) $>> tup2g1

letb
  :: (Avs a, Avs b, Avs c) 
  => Alp a b 
  -> (Alp a b -> Alp a c) 
  -> Alp a c
letb a f = f a

flipA' :: (Avs a, Avs b) => Mvw (Rep (a,b)) (Rep (b,a)) -> Alp (a,b) (b,a)
flipA' w = atomFun (mkMVFun w $ \(a,b) -> (b,a)) (\(a,b) -> (b,a))

flipA :: (Avs a, Avs b) => Alp (a,b) (b,a)
flipA = flipA' mvw

fstE :: (Avs x, Avs a, Avs b) => Alp x (a,b) -> Alp x a
fstE f = f $>> tup2g1

sndE :: (Avs x, Avs a, Avs b) => Alp x (a,b) -> Alp x b
sndE f = f $>> tup2g2
