import Data.Vect

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (eq : EqNat k j) -> EqNat (S k) (S j)
sameS (Same k) = (Same (S k))

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just eq) => Just (cong eq)

myExactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
myExactLength {m} len input = case checkEqNat m len of
                                   Nothing => Nothing
                                   (Just Refl) => Just input

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

same_list : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_list Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  Same3 : (x : _) -> ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (Same3 z) = Same3 (S z)



myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse (x :: xs) = reverseProof x xs (myReverse xs ++ [x])
  where
    reverseProof : (x : elem) -> (xs : Vect len elem) -> Vect (len + 1) elem -> Vect (S len) elem
    reverseProof {len} x xs result = rewrite plusCommutative 1 len in result

test1 : Vect 4 Int
test1 = [1, 2, 3, 4]

test2 : Vect (2 + 2) Int
test2 = test1

append_nil : Vect m elem -> Vect (plus m 0) elem
append_nil {m} xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + len)) elem -> Vect (plus m (S len)) elem
append_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

myAppend : Vect n elem -> Vect m elem -> Vect (m + n) elem
myAppend [] ys = append_nil ys
myAppend (x :: xs) ys = append_xs (x :: myAppend xs ys)

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S n) m = rewrite sym (plusSuccRightSucc m n) in
                                 cong (myPlusCommutes n m)

myBetterReverse : Vect n a -> Vect n a
myBetterReverse xs = myBetterReverse' [] xs
  where
    myBetterReverse' : Vect n a -> Vect m a -> Vect (n + m) a
    myBetterReverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
    myBetterReverse' {n} {m = S len} acc (x :: xs)
      = rewrite sym (plusSuccRightSucc n len) in
                (myBetterReverse' (x :: acc) xs)

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

zeroNotSucc : (0 = S k) -> Void
zeroNotSucc Refl impossible

succNotZero : (S k = 0) -> Void
succNotZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat' Z Z = Yes Refl
checkEqNat' Z (S k) = No zeroNotSucc
checkEqNat' (S k) Z = No succNotZero
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                               (Yes prf) => Yes (cong prf)
                               (No contra) => No (noRec contra)

myExactLength' : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
myExactLength' {m} len input = case decEq m len of
                                    (Yes Refl) => Just input
                                    (No contra) => Nothing


data MyVect : (len : Nat) -> (elem : Type) -> Type where
  Nil : MyVect 0 elem
  (::) : (x : elem) -> (xs : MyVect len elem) -> MyVect (S len) elem

headUnequal : DecEq a => {xs : MyVect n a} -> {ys : MyVect n a} ->
              (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : MyVect n a} -> {ys : MyVect n a} ->
              (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

sameCons : DecEq a => {xs, ys : MyVect n a} -> Dec (xs = ys) -> Dec ((x :: xs) = (x :: ys))
sameCons (Yes Refl) = Yes Refl
sameCons (No contra) = No (tailUnequal contra)

DecEq a => DecEq (MyVect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) =
    case decEq x y of
         (Yes Refl) => sameCons (decEq xs ys)
         (No contra) => No (headUnequal contra)
