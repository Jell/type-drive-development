import Data.Vect

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

removeElem : (value : a) ->
             (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf=Here} = ys
removeElem {n=Z} value (y :: []) {prf=(There later)} = absurd later
removeElem {n=(S k)} value (y :: ys) {prf=(There later)}
  = y :: removeElem value ys {prf=later}


data Elem' : a -> Vect k a -> Type where
     Here : Elem' x (x :: xs)
     There : (later : Elem' x xs) -> Elem' x (y :: xs)

notInNil : Elem' value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (value = x) -> Void) ->
            (notThere : Elem' value xs -> Void) ->
            Elem' value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem' : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem' value xs)
isElem' value [] = No notInNil
isElem' value (x :: xs) = case decEq value x of
                               (Yes Refl) => Yes Here
                               (No notHere) => case (isElem' value xs) of
                                                    (Yes prf) => Yes (There prf)
                                                    (No notThere) => No (notInTail notHere notThere)

elem' : Eq ty => (value : ty) -> (xs : Vect n ty) -> Bool
elem' value [] = False
elem' value (x :: xs) = case value == x of
                             True => True
                             False => elem' value xs


data ElemList : a -> List a -> Type where
  Here' : ElemList x (x :: xs)
  There' : (later : ElemList x xs) -> ElemList x (y :: xs)


notInHead : ElemList x [] -> Void
notInHead Here' impossible
notInHead (There' _) impossible

notInRest : (notHere : (x = y) -> Void) ->
            (notThere : ElemList x xs -> Void) ->
            ElemList x (y :: xs) -> Void
notInRest notHere notThere Here' = notHere Refl
notInRest notHere notThere (There' later) = notThere later

isElemList : DecEq a => (x : a) -> (xs : List a) -> Dec (ElemList x xs)
isElemList x [] = No notInHead
isElemList x (y :: xs) = case decEq x y of
                              (Yes Refl) => Yes Here'
                              (No notHere) => case isElemList x xs of
                                                  (Yes prf) => Yes (There' prf)
                                                  (No notThere) => No (notInRest notHere notThere)


data Last : (xs : List a) -> (x : a) -> Type where
  LastOne : Last [x] x
  LastCons : (later : Last xs x) -> Last (y :: xs) x

emptyNoLast : Last [] x -> Void
emptyNoLast LastOne impossible
emptyNoLast (LastCons _) impossible

notTheLastOne : (contra : (y = x) -> Void) -> Last [y] x -> Void
notTheLastOne contra LastOne = contra Refl

consNotLastNotLast : (contra : Last (z :: xs) x -> Void) -> Last (y :: (z :: xs)) x -> Void
consNotLastNotLast contra (LastCons later) = contra later

isLast : DecEq a => (xs : List a) -> (x : a) -> Dec (Last xs x)
isLast [] x = No emptyNoLast
isLast (y :: []) x = case decEq y x of
                          (Yes Refl) => Yes LastOne
                          (No contra) => No (notTheLastOne contra)
isLast (y :: (z :: xs)) x = case isLast (z :: xs) x of
                                 (Yes prf) => Yes (LastCons prf)
                                 (No contra) => No (consNotLastNotLast contra)
