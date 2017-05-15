%default total

data RunIO : Type -> Type where
     Quit : a -> RunIO a
     Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

greet : RunIO ()
greet = do
  putStr "Enter your name: "
  name <- getLine
  if name == ""
  then do putStrLn "Bye bye!"
          Quit ()
  else do putStrLn ("Hello " ++ name)
          greet

run : RunIO a -> IO (Maybe a)
run (Quit x) = pure (Just x)
run (Do c f) = do res <-c
                  run (f res)

main : IO ()
main = do run greet
          pure ()
