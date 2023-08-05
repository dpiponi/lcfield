import Data.Ratio

infixl 7 *:
infixl 6 +:

type LC' a = [(Rational, a)]

[] +: a = a
a +: [] = a
as@(a@(q, x) : c) +: bs@(b@(r, y) : d) | q < r = a : (c +: bs)
                                       | q > r = b : (as +: d)
                                       | otherwise = (q, x + y) : (c +: d)

(q, a) `lcmono` (r, b) = (q + r, a * b)

a *: [] = []
[] *: b = []
(q : as) *: (r : bs) = (q `lcmono` r) : (map (lcmono q) bs +: map (`lcmono` r) as +: (as *: bs))

lcsign [] = EQ
lcsign ((q, a) : as) | a < 0 = LT
                     | a > 0 = GT
                     | otherwise = lcsign as

lcsignum a = case lcsign a of
  EQ -> []
  LT -> [(0, -1)]
  GT -> [(0, 1)]

lcnegate :: Num a => LC' a -> LC' a
lcnegate = map (\(a, b) -> (a, -b))

lcstar y = let x = (0, 1) : lcnegate (y *: x) in x

lcrecip a =
  lcrecip' (dropWhile (\(q, a) -> a == 0) a)
  where lcrecip' ((q, a) : as) = let u = (-q, recip a) in [u] *: lcstar (map (lcmono u) as)

lcabs [] = []
lcabs x@((q, a) : as) | a < 0 = lcnegate x
                      | a > 0 = x
                      | otherwise = lcabs as

a `lceq` b = lcsign (a +: lcnegate b) == EQ

a `lccompare` b = lcsign (a +: lcnegate b)

data LC a = LC { unLC :: LC' a }

lift1 :: (LC' a -> LC' b) -> LC a -> LC b
lift1 f (LC x) = LC (f x)

lift2 :: (LC' a -> LC' b -> LC' c) -> LC a -> LC b -> LC c
lift2 f (LC x) (LC y) = LC (f x y)

instance (Ord a, Num a) => Num (LC a) where
  (+) = lift2 (+:)
  (*) = lift2 (*:)
  negate = lift1 lcnegate
  abs = lift1 lcabs
  signum = lift1 lcsignum
  fromInteger = i . fromInteger

instance (Ord a, Fractional a) => Fractional (LC a) where
  recip (LC a) = LC (lcrecip a)
  fromRational = i . fromRational

instance (Eq a, Ord a, Num a) => Eq (LC a) where
  LC a == LC b = lceq a b

instance (Ord a, Num a) => Ord (LC a) where
  LC a `compare` LC b = lccompare a b

ε = LC [(1, 1)]

e :: Num a => Rational -> LC a
e q = LC [(q, 1)]

i :: a -> LC a
i x = LC [(0, x)]

main = do
    print $ take 20 $ unLC (1 / (1 + e 1))
    print $ take 20 $ unLC (1 / (1 + e (-1)))
