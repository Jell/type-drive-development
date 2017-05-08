import Data.Vect

occurrences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurrences item [] = 0
occurrences item (value :: values) =
  case value == item of
       False => occurrences item values
       True => 1 + occurrences item values

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False



data Tree : Type -> Type where
  Empty : Tree elem
  Node : (left : Tree elem) ->
         (val : elem) ->
         (right : Tree elem) ->
         Tree elem

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left val right) (Node left' val' right') =
       left == left' && val == val' && right == right'
  (==) _ _ = False

record Album where
  constructor MkAlbum
  artist : String
  title : String
  year : Integer

help : Album
help = MkAlbum "The Beatles" "Help" 1965

rubbersoul : Album
rubbersoul = MkAlbum "The Beatles" "Rubber Soul" 1965

clouds : Album
clouds = MkAlbum "Joni Mitchell" "Clouds" 1969

hunkydory : Album
hunkydory = MkAlbum "David Bowie" "Hunky Dory" 1971

heroes : Album
heroes = MkAlbum "David Bowie" "Heroes" 1977

collection : List Album
collection = [help, rubbersoul, clouds, hunkydory, heroes]

Eq Album where
  (==) (MkAlbum artist title year) (MkAlbum artist' title' year') =
    artist == artist' && title == title' && year == year'

Ord Album where
  compare (MkAlbum artist title year) (MkAlbum artist' title' year') =
    case compare artist artist' of
         EQ => case compare year year' of
                    EQ => compare title title'
                    diff_year => diff_year
         diff_artist => diff_artist


data Shape : Type where
  Triangle : (base : Double) -> (height : Double) -> Shape
  Rectangle : (length : Double) -> (height : Double) -> Shape
  Circle : (radius : Double) -> Shape

area : Shape -> Double
area (Triangle base height) = base * height / 2
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Eq Shape where
  (==) (Triangle base height) (Triangle base' height') =
    base == base' && height == height'
  (==) (Rectangle length height) (Rectangle length' height') =
    length == length' && height == height'
  (==) (Circle radius) (Circle radius') =
    radius == radius'
  (==) _ _ = False

Ord Shape where
  compare x y = compare (area x) (area y)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4,
              Rectangle 2 7]

Show Album where
  show (MkAlbum artist title year) =
    title ++ " by " ++ artist ++ " (released " ++ show year ++ ")"

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

Cast (Maybe elem) (List elem) where
  cast Nothing = []
  cast (Just x) = [x]

Show num => Show (Expr num) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Abs x) = "(abs " ++ show x ++ ")"

(Integral num, Neg num, Eq num) => Eq (Expr num) where
  (==) x y = eval x == eval y


(Integral num, Neg num, Eq num) => Cast (Expr num) num where
  cast orig = eval orig


Functor Tree where
  map func Empty = Empty
  map func (Node left val right) = Node (map func left)
                                        (func val)
                                        (map func right)

Foldable Tree where
  foldr func acc Empty = acc
  foldr func acc (Node left val right) =
    let leftfold = (foldr func acc left)
        rightfold = (foldr func leftfold right) in
        func val rightfold

Functor Expr where
  map func (Val x) = (Val (func x))
  map func (Add x y) = (Add (map func x) (map func y))
  map func (Sub x y) = (Sub (map func x) (map func y))
  map func (Mul x y) = (Mul (map func x) (map func y))
  map func (Div x y) = (Div (map func x) (map func y))
  map func (Abs x) = (Abs (map func x))

data MyVect : (len : Nat) -> (elem : Type) -> Type where
  Nil : MyVect 0 elem
  (::) : (x : elem) -> (xs : MyVect len elem) -> MyVect (S len) elem

Eq a => Eq (MyVect n a) where
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (MyVect n) where
  foldr func acc [] = acc
  foldr func acc (x :: xs) = foldr func (func x acc) xs
