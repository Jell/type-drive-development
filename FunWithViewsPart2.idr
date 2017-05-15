import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views

mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) =
    merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] input2 | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc rec1) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc rec1) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc rec1) | (Snoc rec2)
      = let rest = (equalSuffix xs ys | rec1 | rec 2) in
        if x == y then rest ++ [x] else rest

mergeSort' : Ord a => Vect n a -> Vect n a
mergeSort' input with (splitRec input)
  mergeSort' [] | SplitRecNil = []
  mergeSort' [x] | SplitRecOne = [x]
  mergeSort' (xs ++ ys) | (SplitRecPair lrec rrec)
    = merge (mergeSort' xs | lrec) (mergeSort' ys | rrec)


toBinary : Nat -> String
toBinary input with (halfRec input)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"


palindrome : List Char -> Bool
palindrome input with (vList input)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (xs ++ [y])) | (VCons rec)
    = if x == y then (palindrome xs | rec)
                else False
