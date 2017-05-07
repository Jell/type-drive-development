import Data.Vect

allLengths : Vect n String -> Vect n Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs

xor : Bool -> Bool -> Bool
xor False y = y
xor True y = not y


concat : Vect n a -> Vect m a -> Vect (n + m) a
concat [] ys = ys
concat (x :: xs) ys = x :: concat xs ys


insert : Ord a => (x : a) -> (xsSorted : Vect len a) -> Vect (S len) a
insert x [] = [x]
insert x (y :: xs) = if x <= y
                     then x :: y :: xs
                     else y :: insert x xs

insSort : Ord a => Vect n a -> Vect n a
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs in
                    insert x xsSorted


my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = S (my_length xs)


my_concat : List a -> List a -> List a
my_concat [] ys = ys
my_concat (x :: xs) ys = x :: my_concat xs ys

my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = my_concat (my_reverse xs) [x]

my_map : (a -> b) -> List a -> List b
my_map f [] = []
my_map f (x :: xs) = f x :: my_map f xs

my_vect_map : (a -> b) -> Vect n a -> Vect n b
my_vect_map f [] = []
my_vect_map f (x :: xs) = f x :: my_vect_map f xs

my_vect_map_bis : (a -> b) -> Vect n a -> Vect n b
my_vect_map_bis f [] = []
my_vect_map_bis f (x :: xs) = f x :: my_vect_map_bis f xs

createEmpties : Vect n (Vect 0 elem)
createEmpties {n = Z} = []
createEmpties {n = (S k)} = [] :: createEmpties

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)

addMat : Num a => Vect m (Vect n a) -> Vect m (Vect n a) -> Vect m (Vect n a)
addMat xs ys = zipWith (zipWith (+)) xs ys

dotProduct : Num a => Vect n a -> Vect n a -> a
dotProduct xs ys = sum (zipWith (*) xs ys)

multMatTranspose : Num a => (xs : Vect n (Vect m a)) -> (ys : Vect p (Vect m a)) -> Vect n (Vect p a)
multMatTranspose [] ys = []
multMatTranspose (x :: xs) ys = (map (dotProduct x) ys) :: multMatTranspose xs ys

multMat : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMat xs ys = let yst = transposeMat ys in
                multMatTranspose xs yst


my_length_vect : {n : Nat} -> Vect n a -> Nat
my_length_vect {n} _ = n

my_inner_type : {a : Type} -> Vect n a -> Type
my_inner_type {a} _ = a

mutual
  isEven : Nat -> Bool
  isEven Z = True
  isEven (S k) = isOdd k

  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S k) = isEven k
