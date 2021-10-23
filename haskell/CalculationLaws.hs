module CalculationLaws where

import Lens
import LensComb


-- auxiliary functions for bidirectional fold fusion
blistF :: v -> CLens v t -> CLens (Either () (s, v)) (Either () (s, t))
blistF b0 l = CLens g p
  where
    g (Left ())                        = Left ()
    g (Right (a, b))                   = Right (a, get l b)
    p _ (Left ())                      = Left ()
    p (Right (a, b)) (Right (a', c'))  = Right (a', put l b c')
    p (Left ()) (Right (a', c'))       = Right (a', put l b0 c')

-- auxiliary functions for bidirectional map fusion
infixl 9 ##
(##) :: (s -> CLens s v) -> (v -> CLens v t) -> (s -> CLens s t)
l1 ## l2 = \ a -> l1 a # l2 (get (l1 a) a)

-- auxiliary functions for bidirectional fold-map fusion
bmapF l = CLens g p
  where
    g (Left ())                        = Left ()
    g (Right (a, c))                   = Right (get l a, c)
    p (Left ()) (Left ())              = Left ()
    p (Right (a, c)) (Right (b', c'))  = Right (put l a b', c')
