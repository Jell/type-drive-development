import Data.Vect

append1 : Vect n a -> Vect m a -> Vect (n + m) a
append1 [] ys = ys
append1 (x :: xs) ys = x :: append1 xs ys


append2 : Vect n a -> Vect m a -> Vect (m + n) a
append2 [] [] = []
append2 [] (x :: xs) = x :: append2 [] xs
append2 (x :: xs) [] = x :: xs
append2 (x :: xs) (y :: ys) = y :: append2 (y :: xs) ys


append3 : Vect n a -> Vect m a -> Vect (n + m) a
append3 [] [] = []
append3 [] (x :: xs) = x :: xs
append3 (x :: xs) [] = x :: append3 xs []
append3 (x :: xs) (y :: ys) = y :: append3 xs (y :: ys)
