module StringProcess where

import Data.Char
import Lens
import LensComb
import CalculationLaws

----------------------------------------------------------------
-- String Formatting
----------------------------------------------------------------

bformatting = bfilter (not . isDigit) # bmap' btoUpper

btoUpper :: CLens Char Char
btoUpper = CLens toUpper putToLower

putToLower x y = if isUpper x then y else toLower y

-- optimized version:
bformatting' = bfoldr balg
  where
    balg :: CLens (Either () (Char , [Char])) [Char]
    balg = CLens g p
      where
        g (Left ()) = []
        g (Right (x , xs)) = if not (isDigit x) then toUpper x : xs else xs
        p (Left ()) _ = Left ()
        p (Right (x , xs)) (x' : xs') = if not (isDigit x)
            then Right (putToLower x x', xs')
            else Right (x, x' : xs')
        p (Right (x , xs)) [] = if not (isDigit x) then Left () else Right (x , [])

----------------------------------------------------------------
-- String Encoding and Decoding
----------------------------------------------------------------

bcompression :: CLens [String] [Int]
bcompression =
    bmap' bencode
  # bmap' bascii
  # bfoldr' bcat

bencode = CLens (\ws -> (head ws, length ws)) (\ _ (a, n) -> replicate n a)
-- bascii = bfst (CLens ord (const chr))
bascii = CLens (\ (x, y) -> (ord x, y)) (\ _ (x, y) -> (chr x, y))
bcat = CLens g p
  where
    g (Left ()) = []
    g (Right ((x, y), b)) = x : y : b
    p (Left ()) [] = Left ()
    p (Right _) (x:y:b) = Right ((x, y), b)

-- optimized version
bcompression' = bfoldr' (bmapF (bencode # bascii) # bcat)