{-# LANGUAGE RankNTypes #-}

module LensComb where

import Lens

----------------------------------------------------------------
-- * Bidirectional fold
----------------------------------------------------------------

-- inefficient implementation:
bfoldr_inefficient :: CLens (Either () (s,v)) v -> CLens [s] v
bfoldr_inefficient l = CLens g p
  where
    g = foldr' (get l)
    p = curry $ unfoldr' coalg
      where
        coalg ([],b) = case put l (Left ()) b of
          Left () -> Left ()
          Right (a',b') -> Right (a', ([],b'))
        coalg (a:as,b) = case put l (Right (a, g as)) b of
          Left () -> Left ()
          Right (a', b') -> Right (a', (as,b'))

-- efficicent implementation:
bfoldr :: CLens (Either () (s,v)) v -> CLens [s] v
bfoldr l = CLens (foldr' (get l)) p
  where
    p as b' = let bs = tail $ scanr (\ a b -> get l (Right(a, b))) (get l (Left())) as
              in go as bs b'
    go [] [] b' = case put l (Left ()) b' of
                              Left () -> []
                              Right (a', bim') -> a' : go [] [] bim'
    go (a:as) (bim:bs) b' = case put l (Right (a, bim)) b' of
                              Left () -> []
                              Right (a', bim') -> a' : go as bs bim'

bfoldr' :: CLens (Either () (s,v)) v -> CLens [s] v
bfoldr' = bfoldr

----------------------------------------------------------------
-- * Bidirectional filter
----------------------------------------------------------------

bfilterAlg :: (a -> Bool)
           -> CLens (Either () (a , [a])) [a]
bfilterAlg pr = CLens g p
    where
        g (Left ()) = []
        g (Right (x , xs)) = if pr x then x : xs else xs
        p (Left ()) _ = Left ()
        -- p (Right (x , xs)) (x' : xs') = if pr x then Right (x', xs') else Right (x, x' : xs')
        -- p (Right (x , xs)) [] = if pr x then Left () else Right (x , [])
        p (Right (x , xs)) xs' = if pr x then Right (head xs', tail xs') else Right (x, xs')

bfilter :: (a -> Bool) -> CLens [a] [a]
bfilter pr = bfoldr' (bfilterAlg pr)

----------------------------------------------------------------
-- * Bidirectional map
----------------------------------------------------------------

bmap :: CLens s v -> CLens [s] [v]
bmap l = CLens g p
  where
    g = map (get l)
    p as bs' = map (\ (x, y) -> put l x y) (zip as bs')

bmap_foldr :: CLens s v -> CLens [s] [v]
bmap_foldr l = bfoldr' (CLens g p)
  where
    g (Left ()) = []
    g (Right (a, bs)) = get l a : bs
    p (Left ()) [] = Left ()
    p (Right (a, _)) (a':bs') = Right (put l a a', bs')

bmap' :: CLens s v -> CLens [s] [v]
bmap' = bmap

bmapdep :: (forall x y . Scan x y) -> s
        -> (s -> CLens s v)
        -> CLens [s] [v]
bmapdep scan a0 l = CLens g p
  where
    g as = map (\ (a', a) -> get (l a') a) (zip (a0 : init as) as)
    p as bs' = scan f a0 (zip as bs')
    f (a, b') a' = put (l a') a b'

bmapl :: s
      -> (s -> CLens s v)
      -> CLens [s] [v]
bmapl = bmapdep scanl'

bmapr :: s
      -> (s -> CLens s v)
      -> CLens [s] [v]
bmapr = bmapdep scanr'

bfoldlInit :: v
           -> (v -> CLens (Either () (s, v)) v)
           -> ([s] -> CLens [s] v)
bfoldlInit b0 l as = CLens g p
    where
      g = foldl (\b a -> get (l b) (Right(a, b))) b0
      p [] b' = case put (l (g as)) (Left ()) b' of
                  -- Left () -> error "Left is invalid"
                  Right (a, _) -> as ++ [a]
      p as' b' = case put (l (g as)) (Right (last as', g (init as'))) b' of
                  -- Left () -> error "Left is invalid"
                  Right (a, _) -> as ++ [a]


----------------------------------------------------------------
-- * Bidirectional scan
----------------------------------------------------------------

bscan :: (forall t1 t2 . Scan t1 t2)
      -> v
      -> (v -> CLens (Either () (s, v)) v)
      -> CLens [s] [v]
bscan scan b0 l = CLens g p
  where
    g = scan (\a b -> get (l b) (Right(a, b))) b0
    p as bs' = map (\((a, b), (b'', b')) -> fstRight (put (l b'') (Right(a, b)) b')) abb
      where
        bs = g as
        abb = zip (zip as (b0 : init bs)) (zip (b0 : init bs') bs')
        -- fstRight (Left ()) = error "Left is invalid"
        fstRight (Right (x, _)) = x

bscanl :: v
       -> (v -> CLens (Either () (s, v)) v)
       -> CLens [s] [v]
bscanl = bscan scanl'

bscanr :: v
       -> (v -> CLens (Either () (s, v)) v)
       -> CLens [s] [v]
bscanr = bscan scanr'



