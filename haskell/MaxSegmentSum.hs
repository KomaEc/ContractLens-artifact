module MaxSegmentSum where

import Lens
import LensComb
import CalculationLaws
import SmallExamples (bmax, bmaximum, inf)

type TailsList a = [[a]]

---------------------------------------------------------------

binits :: CLens [a] [[a]]
binits = CLens g p
  where
    g = inits'
    p _ as = if null as then [] else last as

---------------------------------------------------------------

btailsInit :: [a] -> CLens [a] (TailsList a)
btailsInit a = CLens g p
  where
    g = tails'
    p _ v = head v

---------------------------------------------------------------

bmapSum :: Num a => TailsList a -> CLens (TailsList a) [a]
bmapSum xss = CLens g p
  where
    g = map sum
    p _ xs = map (\t -> t ++ [last xs]) xss ++ [[last xs]]

---------------------------------------------------------------

bmaximum2 :: (Num a, Ord a) => [a] -> CLens [a] a
bmaximum2 as = CLens g p
  where
    g = maximum
    p _ x = let t = as ++ [0] in map (+ (x - maximum t)) t

---------------------------------------------------------------

boplus :: (Num a, Ord a) => a -> CLens (Either () (a, a)) a
boplus c = CLens g p
  where
    g (Left()) = -inf
    g (Right(x, y)) = max (x+y) x
    p _ t = Right(t - max c 0, c)

---------------------------------------------------------------

mss :: CLens [Integer] Integer
mss = binits
  # (bmapl [] btailsInit)
  # (bmapl [] bmapSum)
  # (bmapl [] bmaximum2)
  # bmaximum

-- optimized version
mss' :: CLens [Integer] Integer
mss' = bscanl (-inf) boplus # bmaximum


----------------------------------------------------------------
-- test

testmss :: [Integer] -> Integer -> IO()
testmss s v5' = do
  putStrLn "----------------------------------------"
  putStrLn $ "source:\n " ++ show s
  putStrLn $ "inits:\n " ++ show v1
  putStrLn $ "map tails:\n " ++ show v2
  putStrLn $ "map (map sum):\n " ++ show v3
  putStrLn $ "map maximum:\n " ++ show v4
  putStrLn $ "maximum:\n " ++ show v5
  putStrLn "----------------------------------------"
  putStrLn $ "new view:\n " ++ show v5'
  putStrLn $ "~ maximum:\n " ++ show v4'
  putStrLn $ "~ map maximum:\n " ++ show v3'
  putStrLn $ "~ map (map sum):\n " ++ show v2'
  putStrLn $ "~ map tails:\n " ++ show v1'
  putStrLn $ "~ inits:\n " ++ show s'
  putStrLn "----------------------------------------"
  where
    l1 = binits
    l2 = (bmapl [] btailsInit)
    l3 = (bmapl [] bmapSum)
    l4 = (bmapl [] bmaximum2)
    l5 = bmaximum
    v1 = get l1 s
    v2 = get l2 v1
    v3 = get l3 v2
    v4 = get l4 v3
    v5 = get l5 v4
    v4' = put l5 v4 v5'
    v3' = put l4 v3 v4'
    v2' = put l3 v2 v3'
    v1' = put l2 v1 v2'
    s' = put l1 s v1'

testmss' :: [Integer] -> Integer -> IO()
testmss' s v' = do
  putStrLn "----------------------------------------"
  putStrLn $ "source:\n " ++ show s
  putStrLn $ "scan otimes:\n" ++ show v1
  putStrLn $ "maximum:\n" ++ show v2
  putStrLn "----------------------------------------"
  putStrLn $ "new view:\n" ++ show v'
  putStrLn $ "~ maximum:\n" ++ show v1'
  putStrLn $ "~ scan otimes:\n" ++ show s'
  putStrLn "----------------------------------------"
  where
    l1 = bscanl 0 boplus
    l2 = bmaximum
    v1 = get l1 s
    v2 = get l2 v1
    v1' = put l2 v1 v'
    s' = put l1 s v1'

test :: [Integer] -> Integer -> IO()
test s v' = do
  putStrLn "----------------------------------------"
  putStrLn $ "get mss:  " ++ show (get mss s)
  putStrLn $ "get mss': " ++ show (get mss' s)
  putStrLn $ "put mss:  " ++ show (put mss s v')
  putStrLn $ "put mss': " ++ show (put mss' s v')

---------------------------------------------------------------
