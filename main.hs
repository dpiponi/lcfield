{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveTraversable #-}

import Data.Ratio
import Data.List
import Control.Arrow

type PreLC a = [(Rational, a)]

infixl 7 *:
infixl 6 +:

(+:) :: Num a => PreLC a -> PreLC a -> PreLC a
[] +: a  = a
a  +: [] = a
as@(a@(q, x) : as1) +: bs@(b@(r, y) : bs1)
  | q < r     = a          : (as1 +: bs)
  | q > r     = b          : (as  +: bs1)
  | otherwise = (q, x + y) : (as1 +: bs1)

lcprod :: Num a => (Rational, a) -> (Rational, a) -> (Rational, a)
(q, a) `lcprod` (r, b) = (q + r, a * b)

(*:) :: Num a => PreLC a -> PreLC a -> PreLC a
a        *: [] = []
[]       *: b  = []
(q : as) *: (r : bs) =
  (q `lcprod` r) :
  (map (q `lcprod`) bs +: map (`lcprod` r) as +: (as *: bs))

lcnegate :: Num a => PreLC a -> PreLC a
lcnegate = map (second negate)

-- Compute 1/(1-y)
lcstar :: Num a => PreLC a -> PreLC a
lcstar y = let x = (0, 1) : lcnegate (y *: x) in x

lcrecip :: (Eq a, Fractional a) => PreLC a -> PreLC a
lcrecip a = lcrecip' (dropWhile (\(_, a) -> a == 0) a)
  where lcrecip' ((q, a) : as) = let u = (-q, recip a) in [u] *: lcstar (map (lcprod u) as)

lcabs :: (Ord a, Num a) => PreLC a -> PreLC a
lcabs [] = []
lcabs x@((_, a) : as)
  | a < 0 = lcnegate x
  | a > 0 = x
  | otherwise = lcabs as

lcord :: (Ord a, Num a) => PreLC a -> Ordering
lcord [] = EQ
lcord ((_, a) : as)
  | a < 0 = LT
  | a > 0 = GT
  | otherwise = lcord as

lcsignum :: (Ord a, Num a) => PreLC a -> PreLC a
lcsignum a = case lcord a of
  EQ -> []
  LT -> [(0, -1)]
  GT -> [(0, 1)]

lceq :: (Ord a, Num a) => PreLC a -> PreLC a -> Bool
lceq a b = lcord (a +: lcnegate b) == EQ

lccompare :: (Ord a, Num a) => PreLC a -> PreLC a -> Ordering
lccompare a b = lcord (a +: lcnegate b)

newtype LC a = LC (PreLC a)

e ::  Num a => Rational -> LC a
e q = LC [(q, 1)]

ε = e 1

i :: a -> LC a
i x = LC [(0, x)]

lift1 :: (PreLC a -> PreLC b) -> (LC a -> LC b)
lift1 f (LC x) = LC (f x)

lift2 :: (PreLC a -> PreLC b -> PreLC c) -> (LC a -> LC b -> LC c)
lift2 f (LC x) (LC y) = LC (f x y)

instance (Ord a, Num a) => Num (LC a) where
  fromInteger = i . fromInteger

  (+) = lift2 (+:)
  (*) = lift2 (*:)

  negate = lift1 lcnegate
  abs    = lift1 lcabs
  signum = lift1 lcsignum

instance (Ord a, Fractional a) => Fractional (LC a) where
  fromRational = i . fromRational

  recip = lift1 lcrecip

instance (Eq a, Ord a, Num a) => Eq (LC a) where
  LC a == LC b = lceq a b

instance (Ord a, Num a) => Ord (LC a) where
  LC a `compare` LC b = lccompare a b

showTerm :: (Eq a, Ord a, Num a, Show a) => (Rational, a) -> ShowS
showTerm (q, 0) = showString "0"
showTerm (0, a) = showsPrec 7 a
showTerm (q, 1) = showString "e " . showsPrec 8 q
showTerm (q, a) = showsPrec 8 a . showString "*e " . showsPrec 8 q

showSignedTerm :: (Eq a, Ord a, Num a, Show a) => (Rational, a) -> ShowS
showSignedTerm (q, a) | a < 0 = showString "-" . showTerm (q, -a)
showSignedTerm (q, 0) = id
showSignedTerm (q, a) = showString "+" . showTerm (q, a)

showMaybeSignedTerm :: (Eq a, Ord a, Num a, Show a) => (Rational, a) -> ShowS
showMaybeSignedTerm (q, a) | a < 0 = showString "-" . showTerm (q, -a)
showMaybeSignedTerm (q, a) = showTerm (q, a)

showSeries [a] = showSignedTerm a
showSeries (a : as) = showSignedTerm a . showSeries as

showSeriesFromStart [] = showString "0"
showSeriesFromStart [a] = showMaybeSignedTerm a
showSeriesFromStart (a : as) = showMaybeSignedTerm a . showSeries as

instance (Show a, Num a, Ord a) => Show (LC a) where
  showsPrec p (LC a) = showParen (p > 6) $ showSeriesFromStart a

infixl 7 *^

class Vector a v | v -> a where
  (*^) :: a -> v -> v

instance Vector Double Double where
  (*^) = (*)

instance Vector (LC Double) (LC Double) where
  (*^) = (*)

rk4 :: (Fractional a, Vector a v, Num v) => (v -> v) -> a -> v -> v
rk4 f h y = y + ((1 / 6) * h) *^ (k1 + (2 *^ k2) + (2 *^ k3) + k4)
  where  k1 = f y
         k2 = f (y + ((1 / 2) * h *^ k1))
         k3 = f (y + ((1 / 2) * h *^ k2))
         k4 = f (y + (h *^ k3))

data Vec2 a = V a a deriving (Show, Functor)

instance Num a => Num (Vec2 a) where
  V a b + V a' b' = V (a + a') (b + b')
  negate = fmap negate

instance Num a => Vector a (Vec2 a) where
  (*^) a = fmap (a *)

nTimes :: Int -> (a -> a) -> (a -> a)
nTimes 0 f x = x
nTimes n f x = nTimes (n - 1) f (f x)

nSteps = 10
t = pi / 2
dt = t / fromIntegral nSteps

-- Ordinary Runge-Kutta 4 on the reals
test1 :: Vec2 Double
test1 = nTimes nSteps (rk4 (\(V x p) -> V p (-x)) dt) (V 0 1)

-- Runge-Kutta 4 on the Levi-Civita field
test2 :: Vec2 (LC Double)
test2 = nTimes nSteps (rk4 (\(V x p) -> V p (-ω ^ 2 * x)) (i dt)) (V 0 1)
        where ω = 1 + ε

-- Cf. https://www.bmtdynamics.org/pub/papers/ApoDA09/ApoDA09.pdf
--
main = do
    print $ test1
    print $ test2
