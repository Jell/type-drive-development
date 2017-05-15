import Data.Primitives.Views
import System

%default total

data InfList : Type -> Type where
     (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom (x + 1))

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith (value :: xs) [] = []
labelWith (value :: xs) (x :: ys) = (value, x) :: labelWith xs ys

label : List a -> List (Integer, a)
label = labelWith [0..]

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
               (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

partial
quiz : Stream Int -> (score : Nat) -> IO ()
quiz (num1 :: num2 :: nums) score
  = do putStrLn ("Score so far: "++show score)
       putStr (show num1 ++ " * " ++ show num2 ++ "? ")
       answer <- getLine
       if cast answer == num1 * num2
       then do putStrLn "Correct!"
               quiz nums (score + 1)
       else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
               quiz nums score


every_other : Stream a -> Stream a
every_other (_ :: x :: xs) = x :: every_other xs

Functor InfList where
  map func (value :: xs) = (func value) :: map func xs

data Face = Heads | Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z xs = []
coinFlips (S k) (value :: xs) with (divides value 2)
  coinFlips (S k) (((2 * div) + rem) :: xs) | (DivBy prf)
    = (if rem == 0 then Heads else Tails) :: coinFlips k xs

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx
  = let next = (approx + (number / approx)) / 2 in
    next :: square_root_approx number next

square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) -> (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (value :: xs)
  = if (value * value) - number < bound
    then value
    else square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001
                                       (square_root_approx number number)

data InfIO : Type where
     Do : IO a -> (a -> Inf InfIO) -> InfIO

loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)

run : InfIO -> IO ()
run (Do action cont) = do res <- action
                          run (cont res)

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run' : Fuel -> InfIO -> IO ()
run' (More fuel) (Do c f) = do res <- c
                               run' fuel (f res)
run' Dry y = putStrLn "Out of fuel"

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

loopPrint' : String -> InfIO
loopPrint' msg = do putStrLn msg
                    loopPrint msg

quiz' : Stream Int -> (score : Nat) -> InfIO
quiz' (num1 :: num2 :: nums) score
  = do putStrLn ("Score so far: "++show score)
       putStr (show num1 ++ " * " ++ show num2 ++ "? ")
       answer <- getLine
       if cast answer == num1 * num2
       then do putStrLn "Correct!"
               quiz' nums (score + 1)
       else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
               quiz' nums score

partial
main : IO ()
main = do seed <- time
          run' forever (quiz' (arithInputs (fromInteger seed)) 0)



totalREPL : String -> (String -> String) -> InfIO
totalREPL prompt fun = do
  putStr prompt
  line <- getLine
  putStrLn (fun line)
  totalREPL prompt fun
