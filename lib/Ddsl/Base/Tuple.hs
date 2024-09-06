module Ddsl.Base.Tuple where

import Ddsl.Atom
import Ddsl.Symbolic
import Ddsl.Term

unpack3 :: (Avs a, Avs b, Avs c) => Alp (a,b,c) (a,(b,c))
unpack3 = unpack3' mvw

unpack3' :: (Avs a, Avs b, Avs c) => Mvw (Rep (a,b,c)) (Rep (a,(b,c))) -> Alp (a,b,c) (a,(b,c))
unpack3' w = atomFun (mkMVFun w id) (\(a,b,c) -> (a,(b,c)))

pack3 ::  (Avs a, Avs b, Avs c) => Alp (a,(b,c)) (a,b,c)
pack3 = pack3' mvw

pack3' ::  (Avs a, Avs b, Avs c) => Mvw (Rep (a,(b,c))) (Rep (a,b,c)) -> Alp (a,(b,c)) (a,b,c)
pack3' w = atomFun (mkMVFun w id) (\(a,(b,c)) -> (a,b,c))

dup3 :: (Avs a) => Alp a (a,a,a)
dup3 = dup2 $>> tup2o2 dup2 $>> pack3

tup3g1 :: (Avs x, Avs a, Avs b) => Alp (x,a,b) x
tup3g1 = unpack3 $>> tup2g1
tup3g2 :: (Avs x, Avs a, Avs b) => Alp (a,x,b) x
tup3g2 = unpack3 $>> tup2g2 $>> tup2g1
tup3g3 :: (Avs x, Avs a, Avs b) => Alp (a,b,x) x
tup3g3 = unpack3 $>> tup2g2 $>> tup2g2

tup3o1 :: (Avs x1, Avs x2, Avs a, Avs b) => Alp x1 x2 -> Alp (x1,a,b) (x2,a,b)
tup3o1 m = unpack3 $>> tup2o1 m $>> pack3
tup3o2 :: (Avs x1, Avs x2, Avs a, Avs b) => Alp x1 x2 -> Alp (a,x1,b) (a,x2,b)
tup3o2 m = unpack3 $>> tup2o2 (tup2o1 m) $>> pack3
tup3o3 :: (Avs x1, Avs x2, Avs a, Avs b) => Alp x1 x2 -> Alp (a,b,x1) (a,b,x2)
tup3o3 m = unpack3 $>> tup2o2 (tup2o2 m) $>> pack3

tup3 :: (Avs a, Avs b, Avs c, Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x (a,b,c)
tup3 m1 m2 m3 =
  dup3
  $>> tup3o1 m1
  $>> tup3o2 m2
  $>> tup3o3 m3

unpack4 :: (Avs a, Avs b, Avs c, Avs d) => Alp (a,b,c,d) (a,(b,(c,d)))
unpack4 = unpack4' mvw

unpack4' :: (Avs a, Avs b, Avs c, Avs d) => Mvw (Rep (a,b,c,d)) (Rep (a,(b,(c,d)))) -> Alp (a,b,c,d) (a,(b,(c,d)))
unpack4' w = atomFun (mkMVFun w id) (\(a,b,c,d) -> (a,(b,(c,d))))

pack4 :: (Avs a, Avs b, Avs c, Avs d) => Alp (a,(b,(c,d))) (a,b,c,d)
pack4 = pack4' mvw

pack4' :: (Avs a, Avs b, Avs c, Avs d) => Mvw (Rep (a,(b,(c,d)))) (Rep (a,b,c,d)) -> Alp (a,(b,(c,d))) (a,b,c,d)
pack4' w = atomFun (mkMVFun w id) (\(a,(b,(c,d))) -> (a,b,c,d))

dup4 :: (Avs a) => Alp a (a,a,a,a)
dup4 = dup2 $>> tup2o2 (dup2 $>> tup2o2 dup2) $>> pack4

unpack5
  :: (Avs a, Avs b, Avs c, Avs d, Avs e)
  => Alp (a,b,c,d,e) (a,(b,(c,(d,e))))
unpack5 = unpack5' mvw

unpack5'
  :: (Avs a, Avs b, Avs c, Avs d, Avs e)
  => Mvw (Rep (a,b,c,d,e)) (Rep (a,(b,(c,(d,e)))))
  -> Alp (a,b,c,d,e) (a,(b,(c,(d,e))))
unpack5' w = atomFun (mkMVFun w id) (\(a,b,c,d,e) -> (a,(b,(c,(d,e)))))

pack5
  :: (Avs a, Avs b, Avs c, Avs d, Avs e)
  => Alp (a,(b,(c,(d,e)))) (a,b,c,d,e)
pack5 = pack5' mvw

pack5'
  :: (Avs a, Avs b, Avs c, Avs d, Avs e)
  => Mvw (Rep (a,(b,(c,(d,e))))) (Rep (a,b,c,d,e))
  -> Alp (a,(b,(c,(d,e)))) (a,b,c,d,e)
pack5' w = atomFun (mkMVFun w id) (\(a,(b,(c,(d,e)))) -> (a,b,c,d,e))

dup5 :: (Avs a) => Alp a (a,a,a,a,a)
dup5 = dup2 $>> tup2o2 (dup2 $>> tup2o2 (dup2 $>> tup2o2 dup2)) $>> pack5

from2
  :: (Avs a, Avs b, Avs c)
  => (Alp (a,b) a -> Alp (a,b) b -> Alp (a,b) c)
  -> Alp (a,b) c
from2 f = f tup2g1 tup2g2

from2'
  :: (Avs a, Avs b, Avs c, Avs x)
  => Alp x (a,b)
  -> (Alp x a -> Alp x b -> Alp x c)
  -> Alp x c
from2' m f = f (m $>> tup2g1) (m $>> tup2g2)

from3'
  :: (Avs a, Avs b, Avs c, Avs d, Avs x)
  => Alp x (a,b,c)
  -> (Alp x a -> Alp x b -> Alp x c -> Alp x d)
  -> Alp x d
from3' m f = f (m $>> tup3g1) (m $>> tup3g2) (m $>> tup3g3)

from3
  :: (Avs a, Avs b, Avs c, Avs d)
  => (Alp (a,b,c) a -> Alp (a,b,c) b -> Alp (a,b,c) c -> Alp (a,b,c) d)
  -> Alp (a,b,c) d
from3 = from3' input

tup4g1 :: (Avs x, Avs a, Avs b, Avs c) => Alp (x,a,b,c) x
tup4g1 = unpack4 $>> tup2g1
tup4g2 :: (Avs x, Avs a, Avs b, Avs c) => Alp (a,x,b,c) x
tup4g2 = unpack4 $>> tup2g2 $>> tup2g1
tup4g3 :: (Avs x, Avs a, Avs b, Avs c) => Alp (a,b,x,c) x
tup4g3 = unpack4 $>> tup2g2 $>> tup2g2 $>> tup2g1
tup4g4 :: (Avs x, Avs a, Avs b, Avs c) => Alp (a,b,c,x) x
tup4g4 = unpack4 $>> tup2g2 $>> tup2g2 $>> tup2g2

tup4o1 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c) => Alp x1 x2 -> Alp (x1,a,b,c) (x2,a,b,c)
tup4o1 m = unpack4 $>> tup2o1 m $>> pack4
tup4o2 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c) => Alp x1 x2 -> Alp (a,x1,b,c) (a,x2,b,c)
tup4o2 m = unpack4 $>> tup2o2 (tup2o1 m) $>> pack4
tup4o3 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c) => Alp x1 x2 -> Alp (a,b,x1,c) (a,b,x2,c)
tup4o3 m = unpack4 $>> tup2o2 (tup2o2 (tup2o1 m)) $>> pack4
tup4o4 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c) => Alp x1 x2 -> Alp (a,b,c,x1) (a,b,c,x2)
tup4o4 m = unpack4 $>> tup2o2 (tup2o2 (tup2o2 m)) $>> pack4

from4'
  :: (Avs a, Avs b, Avs c, Avs d, Avs e, Avs x)
  => Alp x (a,b,c,d)
  -> (Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e)
  -> Alp x e
from4' m f = f
  (m $>> tup4g1)
  (m $>> tup4g2)
  (m $>> tup4g3)
  (m $>> tup4g4)

from4
  :: (Avs a, Avs b, Avs c, Avs d, Avs e)
  => (Alp (a,b,c,d) a -> Alp (a,b,c,d) b -> Alp (a,b,c,d) c -> Alp (a,b,c,d) d -> Alp (a,b,c,d) e)
  -> Alp (a,b,c,d) e
from4 = from4' input

tup4 :: (Avs a, Avs b, Avs c, Avs d, Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x (a,b,c,d)
tup4 m1 m2 m3 m4 =
  dup4
  $>> tup4o1 m1
  $>> tup4o2 m2
  $>> tup4o3 m3
  $>> tup4o4 m4

tup5g1 :: (Avs x, Avs a, Avs b, Avs c, Avs d) => Alp (x,a,b,c,d) x
tup5g1 = unpack5 $>> tup2g1
tup5g2 :: (Avs x, Avs a, Avs b, Avs c, Avs d) => Alp (a,x,b,c,d) x
tup5g2 = unpack5 $>> tup2g2 $>> tup2g1
tup5g3 :: (Avs x, Avs a, Avs b, Avs c, Avs d) => Alp (a,b,x,c,d) x
tup5g3 = unpack5 $>> tup2g2 $>> tup2g2 $>> tup2g1
tup5g4 :: (Avs x, Avs a, Avs b, Avs c, Avs d) => Alp (a,b,c,x,d) x
tup5g4 = unpack5 $>> tup2g2 $>> tup2g2 $>> tup2g2 $>> tup2g1
tup5g5 :: (Avs x, Avs a, Avs b, Avs c, Avs d) => Alp (a,b,c,d,x) x
tup5g5 = unpack5 $>> tup2g2 $>> tup2g2 $>> tup2g2 $>> tup2g2

tup5o1 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs d) => Alp x1 x2 -> Alp (x1,a,b,c,d) (x2,a,b,c,d)
tup5o1 m = unpack5 $>> tup2o1 m $>> pack5
tup5o2 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs d) => Alp x1 x2 -> Alp (a,x1,b,c,d) (a,x2,b,c,d)
tup5o2 m = unpack5 $>> tup2o2 (tup2o1 m) $>> pack5
tup5o3 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs d) => Alp x1 x2 -> Alp (a,b,x1,c,d) (a,b,x2,c,d)
tup5o3 m = unpack5 $>> tup2o2 (tup2o2 (tup2o1 m)) $>> pack5
tup5o4 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs d) => Alp x1 x2 -> Alp (a,b,c,x1,d) (a,b,c,x2,d)
tup5o4 m = unpack5 $>> tup2o2 (tup2o2 (tup2o2 (tup2o1 m))) $>> pack5
tup5o5 :: (Avs x1, Avs x2, Avs a, Avs b, Avs c, Avs d) => Alp x1 x2 -> Alp (a,b,c,d,x1) (a,b,c,d,x2)
tup5o5 m = unpack5 $>> tup2o2 (tup2o2 (tup2o2 (tup2o2 m))) $>> pack5

from5'
  :: (Avs a, Avs b, Avs c, Avs d, Avs e, Avs f, Avs x)
  => Alp x (a,b,c,d,e)
  -> (Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e -> Alp x f)
  -> Alp x f
from5' m f = f
  (m $>> tup5g1)
  (m $>> tup5g2)
  (m $>> tup5g3)
  (m $>> tup5g4)
  (m $>> tup5g5)

from5
  :: (Avs a, Avs b, Avs c, Avs d, Avs e, Avs f)
  => (Alp (a,b,c,d,e) a -> Alp (a,b,c,d,e) b -> Alp (a,b,c,d,e) c -> Alp (a,b,c,d,e) d -> Alp (a,b,c,d,e) e -> Alp (a,b,c,d,e) f)
  -> Alp (a,b,c,d,e) f
from5 = from5' input

tup5 :: (Avs a, Avs b, Avs c, Avs d, Avs e, Avs x) => Alp x a -> Alp x b -> Alp x c -> Alp x d -> Alp x e -> Alp x (a,b,c,d,e)
tup5 m1 m2 m3 m4 m5 =
  dup5
  $>> tup5o1 m1
  $>> tup5o2 m2
  $>> tup5o3 m3
  $>> tup5o4 m4
  $>> tup5o5 m5
