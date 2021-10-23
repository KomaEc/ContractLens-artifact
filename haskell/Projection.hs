module Projection where

import Lens
import LensComb

bproj :: CLens [Float] [Float]
bproj = bmean # bdiff

bmean :: CLens [Float] (Float, [Float])
bmean  = CLens g p where  g xs = (mean xs, xs)
                          p _ (m, xs') = xs'

bdiff :: CLens (Float, [Float]) [Float]
bdiff  = CLens g p where  g (m, xs) = map (+(-m)) xs
                          p (m, _) xs' = (m, map (+m) xs')

mean :: [Float] -> Float
mean xs = sum xs / fromIntegral (length xs)