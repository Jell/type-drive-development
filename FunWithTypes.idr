import Data.Vect

data Direction = North
               | East
               | South
               | West

turnClockwise : Direction -> Direction
turnClockwise North = East
turnClockwise East = South
turnClockwise South = West
turnClockwise West = North

data Shape : Type where
  Triangle : (base : Double) -> (height : Double) -> Shape
  Rectangle : (length : Double) -> (height : Double) -> Shape
  Circle : (radius : Double) -> Shape

area : Shape -> Double
area (Triangle base height) = base * height / 2
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

data Picture : Type where
  Primitive : (primitive : Shape) -> Picture
  Combine : (pic1 : Picture) -> (pic2 : Picture) -> Picture
  Rotate : (angle : Double) -> (pic : Picture) -> Picture
  Translate : (transX : Double) -> (transY : Double) -> (pic : Picture) -> Picture


rectangle : Picture
rectangle = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

triangle : Picture
triangle = Primitive (Triangle 10 10)

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                      (Combine (Translate 35 5 circle)
                               (Translate 15 25 triangle))

pictureArea : Picture -> Double
pictureArea (Primitive primitive) = area primitive
pictureArea (Combine pic1 pic2) = pictureArea pic1 + pictureArea pic2
pictureArea (Rotate angle pic) = pictureArea pic
pictureArea (Translate transX transY pic) = pictureArea pic


data BSTree : Type -> Type where
  Empty : Ord elem => BSTree elem
  Node : Ord elem => (left : BSTree elem) -> (val : elem) -> (right : BSTree elem) -> BSTree elem

insert : elem -> BSTree elem -> BSTree elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right) =
  case (compare x val) of
       LT => Node (insert x left) val right
       EQ => orig
       GT => Node left val (insert x right)


listToTree : Ord elem => List elem -> BSTree elem
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

treeToList : BSTree elem -> List elem
treeToList Empty = []
treeToList (Node left val right) = (treeToList left) ++ [val] ++ (treeToList right)

data Expr : Type where
  SomeInt : Int -> Expr
  Add : Expr -> Expr -> Expr
  Sub : Expr -> Expr -> Expr
  Mul : Expr -> Expr -> Expr

evaluate : Expr -> Int
evaluate (SomeInt x) = x
evaluate (Add x y) = (evaluate x) + (evaluate y)
evaluate (Sub x y) = (evaluate x) - (evaluate y)
evaluate (Mul x y) = (evaluate x) * (evaluate y)

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing y = y
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just (max x y)

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive triangle@(Triangle _ _)) = Just (area triangle)
biggestTriangle (Primitive _) = Nothing
biggestTriangle (Combine pic1 pic2) = maxMaybe (biggestTriangle pic1) (biggestTriangle pic2)
biggestTriangle (Rotate angle pic) = biggestTriangle pic
biggestTriangle (Translate transX transY pic) = biggestTriangle pic

data Energy = Petrol | Electric

data PowerSource = Pedal | Fuel Energy

data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Unicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle (Fuel e)
  Bus : (fuel : Nat) -> Vehicle (Fuel e)
  Motorcycle : (fuel : Nat) -> Vehicle (Fuel e)


wheels : Vehicle power -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels (Motorcycle fuel) = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4

refuel : Vehicle (Fuel e) -> Vehicle (Fuel e)
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 50

my_append : Vect n elem -> Vect m elem -> Vect (n + m) elem
my_append [] y = y
my_append (x :: xs) y = x :: my_append xs y

my_zip : Vect n a -> Vect n b -> Vect n (a, b)
my_zip [] [] = []
my_zip (x :: xs) (y :: z) = (x, y) :: my_zip xs z

my_index : Fin n -> Vect n a -> a
my_index FZ (x :: xs) = x
my_index (FS x) (y :: xs) = my_index x xs


try_index : Integer -> Vect n a -> Maybe a
try_index {n} i xs = case integerToFin i n of
                          Just idx => Just (my_index idx xs)
                          Nothing => Nothing

my_take : (m : Fin (S n)) -> Vect n a -> Vect (cast m) a
my_take FZ xs = []
my_take (FS i) (x :: xs) = x :: my_take i xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys =
  case integerToFin pos n of
    Just idx => let lookup = Data.Vect.index idx in
                    Just (lookup xs + lookup ys)
    Nothing => Nothing
