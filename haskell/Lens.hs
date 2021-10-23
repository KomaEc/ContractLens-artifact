module Lens where

----------------------------------------------------------------
-- * Lens
----------------------------------------------------------------

-- Contract Lenses (contracts are omitted in Haskell implementation)
data CLens s v = CLens
    { get :: s -> v
    , put :: s -> v -> s
    }

-- Composition of Contract Lenses
infixl 9 #
(#) :: CLens s v -> CLens v t -> CLens s t
l1 # l2 = CLens g p
  where
    g = get l2 . get l1
    p s t = put l1 s (put l2 (get l1 s) t)


----------------------------------------------------------------
-- * Utilities
----------------------------------------------------------------

type Scan a b = (a -> b -> b) -> b -> [a] -> [b]

scanl' :: Scan a b
scanl' f x = tail . scanl (flip f) x

scanr' :: Scan a b
scanr' f x = init . scanr f x

inits' :: [a] -> [[a]]
inits' = scanl' (\x y -> y ++ [x]) [] -- tail . inits

tails' :: [a] -> [[a]]
tails' = scanr' (:) [] -- init . tails

foldr' :: (Either () (a, b) -> b) -> [a] -> b
foldr' alg  []      = alg (Left ())
foldr' alg  (x:xs)  = alg (Right (x, foldr' alg xs))

unfoldr' :: (b -> Either () (a, b)) -> b -> [a]
unfoldr' coalg b = case coalg b of
                     Left () -> []
                     Right (a, b') -> a : unfoldr' coalg b'

myscanr :: (a -> b -> b) -> b -> [a] -> [b]
myscanr f b0 as = foldr (\ a bs -> (f a (head bs)) : bs) [b0] as