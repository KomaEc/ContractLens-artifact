module SmallExamples where

import Lens
import LensComb
import Data.List (sort)

-- Example 4.2
binits :: CLens [a] [[a]]
binits = CLens g p
  where
    g = inits'
    p _ as = if null as then [] else last as

-- Example 5.1
bmaximum = bfoldr bmax

-- Example 5.2
bmaximum' = bfoldr' bmax

-- for simplicity, we fix the infinity
inf :: Num a => a
inf = 1000

bmax :: (Ord a, Num a) => CLens (Either () (a, a)) a
bmax = CLens g p
  where
    g (Left()) = -inf
    g (Right(x, y)) = max x y
    -- p (Left()) (-inf) = Left()
    -- p (Left()) x = Right(x, -1000)
    p (Left()) x | x == -inf = Left ()
                 | otherwise = Right(x, -inf)
    p (Right(x, y)) t = if x >= y then Right(t, min t y) else Right(min t x, t)

-- Example 5.3
bevens = bfilter even

-- Example 5.4
bdoubles = bmap' bdouble
  where bdouble = CLens (*2) (\ _ v' -> div v' 2)

-- Example 5.5
example55 = bsort # bmapl (-inf) bmod10

bsort :: CLens [Int] [Int]
bsort = CLens g p
  where
    g = sort
    p as bs' = if sort as == bs' then as else bs'


bmod10 :: Int -> CLens Int Int
bmod10 a' = CLens g p
  where
    g a = mod a 10
    p a b = if mod a 10 == b then go a else go b
    go x = if x > a' then x else go (x+10)

-- Example 5.6
bprefixSum :: CLens [Int] [Int]
bprefixSum = binits # bmapl [] (bfoldlInit 0 badd)

badd :: (Num a, Eq a) => a -> CLens (Either () (a, a)) a
badd b = CLens g p
  where
    g (Left ()) = 0
    g (Right(x, y)) = x + y
    p _ s = Right(s-b, b)

-- Example 5.7
bprefixProd :: CLens [Int] [Int]
bprefixProd = bscanl 1 bmul

bmul :: Int -> CLens (Either () (Int, Int)) Int
bmul b = CLens g p
  where
    g (Left ()) = 1
    g (Right (x, y)) = x * y
    p _ b' = Right (div b' b, b)

-- Example 6.1
bprefixProd' :: CLens [Int] [Int]
bprefixProd' = bscanl 0 badd