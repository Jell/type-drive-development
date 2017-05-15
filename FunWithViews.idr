data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (xs : List Int) -> ListLast xs -> String
describeHelper [] Empty = "Empty"
describeHelper (ys ++ [x]) (NonEmpty ys x) =
  "Non empty, initial portion: " ++ (show ys)


total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

describeListEnd' : List Int -> String
describeListEnd' input with (listLast input)
  describeListEnd' [] | Empty = "Empty"
  describeListEnd' (xs ++ [x]) | (NonEmpty xs x) =
    "Non empty, initial portion: " ++ (show xs)


myReverse : List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs


data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights : List a) ->
                 SplitList (lefts ++ rights)

splitList : (input : List a) -> SplitList input
splitList input = splitListHelper input input
  where
    splitListHelper : List a -> (input : List a) -> SplitList input
    splitListHelper _ [] = SplitNil
    splitListHelper _ [x] = SplitOne
    splitListHelper (_ :: _ :: counter) (item :: items)
      = case splitListHelper counter items of
             SplitNil => SplitOne
             SplitOne {x} => SplitPair [item] [x]
             (SplitPair lefts rights) => SplitPair (item :: lefts) rights
    splitListHelper _ items = SplitPair [] items

mergeSort : Ord a => List a -> List a
mergeSort input with (splitList input)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights)
    = merge (mergeSort lefts) (mergeSort rights)

data TakeN : List a -> Type where
     Fewer : TakeN xs
     Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => (Exact (x :: n_xs))

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n input with (takeN n input)
  groupByN n [] | Fewer = []
  groupByN n (x :: xs) | Fewer = [(x :: xs)]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest


halves : List a -> (List a, List a)
halves xs = let n = (length xs) `div` 2 in
            case takeN n xs of
                 Fewer => (xs, [])
                 (Exact n_xs {rest}) => (n_xs, rest)

data SnocList : List a -> Type where
     Empty' : SnocList []
     Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

snocListHelp : (snoc : SnocList input) -> (rest : List a) ->
               SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in  snoc
snocListHelp {input} snoc (x :: xs) = rewrite appendAssociative input [x] xs in
                                      (snocListHelp (Snoc snoc {x}) xs)

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty' xs

myReverseHelper : (input : List a) -> SnocList input -> List a
myReverseHelper [] Empty' = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

myReverse' : List a -> List a
myReverse' input = myReverseHelper input (snocList input)


myReverse'' : List a -> List a
myReverse'' input with (snocList input)
  myReverse'' [] | Empty' = []
  myReverse'' (xs ++ [x]) | (Snoc rec) = x :: myReverse'' xs | rec

isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix [] input2 | Empty' = True
  isSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    isSuffix (xs ++ [x]) [] | (Snoc xsrec) | Empty' = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec)
      = if x == y then isSuffix xs ys | xsrec | ysrec
                  else False

data SplitRec : List a -> Type where
     SplitRecNil : SplitRec []
     SplitRecOne : SplitRec [x]
     SplitRecPair : (lrec : Lazy (SplitRec lefts)) ->
                    (rrec : Lazy (SplitRec rights)) ->
                    SplitRec (lefts ++ rights)
