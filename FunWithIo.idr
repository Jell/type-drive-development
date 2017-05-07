import System
import Data.Vect

printLength : IO ()
printLength = putStr "Input string: " >>= \_ =>
              getLine >>= \input =>
              let len = length input in
              putStrLn (show len)

printLonger : IO ()
printLonger = do
  line1 <- getLine
  line2 <- getLine
  if (length line1) > (length line2)
  then putStrLn line1
  else putStrLn line2

printLongerBis : IO ()
printLongerBis = getLine >>= \line1 =>
                 getLine >>= \line2 =>
                 if (length line1) > (length line2)
                 then putStrLn line1
                 else putStrLn line2

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
  then pure (Just (cast input))
  else pure Nothing


readNumbers : IO (Maybe (Nat, Nat))
readNumbers = do
  Just num1 <- readNumber | Nothing => pure Nothing
  Just num2 <- readNumber | Nothing => pure Nothing
  pure (Just (num1, num2))

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Lift off!"
countdown now@(S remaining) = do
  printLn now
  usleep 1000000
  countdown remaining

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
  putStrLn ("Guesses: "++(show guesses))
  Just n <- readNumber | Nothing => do
    putStrLn "invalid number"
    guess target guesses
  case (compare n target) of
       EQ => putStrLn "You win!"
       LT => do
         putStrLn "Too small"
         guess target (S guesses)
       GT => do
         putStrLn "Too large"
         guess target (S guesses)


guess' : IO ()
guess' = do
  target <- time
  guess (cast (mod target 100)) 0


repl' : String -> (String -> String) -> IO ()
repl' prompt fun = do
  putStr prompt
  line <- getLine
  putStrLn (fun line)
  repl' prompt fun

replWith' : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
replWith' state prompt fun = do
  putStr prompt
  line <- getLine
  case fun state line of
    Nothing => pure ()
    Just (out, new_state) => do
      putStrLn out
      replWith' new_state prompt fun


testReplWith : IO ()
testReplWith = replWith 0 "> " (\s, n => Just ((show s)++": "++n++"\n", (S s)))


data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect : IO (len ** Vect len String)
readVect = do
  x <- getLine
  if (x == "")
  then pure (_ ** [])
  else do (_ ** xs) <- readVect
          pure (_ ** x :: xs)


printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) =
  putStrLn ((show xs) ++ " (length " ++ (show len) ++ ")")

anyVect : (n : Nat ** Vect n String)
anyVect = (_ ** ["a","b","c"])

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter first vector (blank line to end)"
  (len1 ** vec1) <- readVect
  putStrLn "Enter second vector (blank line to end)"
  (len2 ** vec2) <- readVect
  case exactLength len1 vec2 of
       Nothing => putStrLn "Vectors have different lengths"
       Just vec2' => printLn (zip vec1 vec2')


readToBlank : IO (List String)
readToBlank = do
  line <- getLine
  if (line == "")
  then pure []
  else do lines <- readToBlank
          pure (line :: lines)

readAndSave : IO ()
readAndSave = do
    lines <- readToBlank
    putStr "Filename: "
    filename <- getLine
    Right file <- openFile filename WriteTruncate
      | Left err => putStrLn ("failed to open file: " ++ (show err))
    traverse (fPutStrLn file) lines
    closeFile file

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
    Right file <- openFile filename Read
      | Left err => pure (_ ** [])
    vect <- readVect file
    closeFile file
    pure vect
  where
    readVect : File -> IO (m ** Vect m String)
    readVect file = do
      False <- fEOF file
        | True => pure (_ ** [])
      Right line <- fGetLine file
        | Left err => pure (_ ** [])
      (_ ** lines) <- (readVect file)
      pure $ case (trim line) of
                  "" => (_ ** lines)
                  line' => (_ ** line' :: lines)
