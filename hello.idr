module Main

StringOrInt : Bool -> Type
StringOrInt x = case x of
                     True => Int
                     False => String

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = case x of
                        True => 94
                        False => "Ninety four"

valToString : (x : Bool) -> StringOrInt x -> String
valToString x val = case x of
                         True => cast val
                         False => val

average : String -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str)) in
                  cast totalLength / cast numWords
  where
    wordCount : String -> Nat
    wordCount str = length (words str)

    allLengths : List String -> List Nat
    allLengths strs = map length strs

showAverage : String -> String
showAverage str = "The average word length is: " ++
                  show (average str) ++ "\n"


twice : (a -> a) -> (a -> a)
twice f x = f (f x)

double : Num n => n -> n
double n = n + n

quad : Num n => n -> n
quad = twice double

main : IO ()
main = repl "Enter a string: " showAverage
