import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

data Command : Schema -> Type where
  SetSchema : (newschema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : (index : Integer) -> Command schema
  All : Command schema
  Quit : Command schema

testStore : DataStore
testStore = MkData (SString .+. SInt) 1 [("Answer", 42)]


addToStore : (store : DataStore) ->
             (SchemaType (schema store)) ->
             DataStore
addToStore (MkData schema size items) newitem =
  MkData schema _ (addToData items)
    where
      addToData : Vect old (SchemaType schema) ->
                  Vect (S old) (SchemaType schema)
      addToData [] = [newitem]
      addToData (item' :: items') = item' :: addToData items'

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = cast item
display {schema = (x .+. y)} (a, b) = display a ++ ", " ++ display b

getEntry : (pos : Integer) ->
           (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store@(MkData store_schema store_size store_items)
  = case integerToFin pos store_size of
         Nothing => Just ("Out of range\n", store)
         (Just id) => Just ((display (index id store_items)) ++ "\n", store)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema (MkData schema Z []) newschema = Just (MkData newschema _ [])
setSchema _ _ = Nothing

printItems : (items : Vect size (SchemaType schema)) -> String
printItems {size=Z} [] = ""
printItems {size=(S k)} (x :: xs) =
  (printItems xs) ++ (show k) ++ ": " ++ (display x) ++ "\n"

printStore : (store : DataStore) -> String
printStore store = printItems (reverse (items store))

parsePrefix : (schema : Schema) ->
              String ->
              (Maybe (SchemaType schema, String))
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) =
      case span (/= '"') xs of
        (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
        _ => Nothing
    getQuoted _ = Nothing
parsePrefix SInt input = case span isDigit input of
                              ("", rest) => Nothing
                              (num, rest) => Just (cast num, ltrim rest)
parsePrefix SChar input = case (unpack input) of
                               ' ' :: rest => Nothing
                               c :: rest => Just (c, (ltrim (pack rest)))
                               _ => Nothing
parsePrefix (schemal .+. schemar) input = do
  (l_val, input') <- parsePrefix schemal input
  (r_val, input'') <- parsePrefix schemar input'
  pure ((l_val, r_val), input'')

parseBySchema : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema)
parseBySchema schema str = case parsePrefix schema str of
                                Just (res, "") => Just res
                                Just _ => Nothing
                                Nothing => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: []) = Just SString
parseSchema ("String" :: xs) = (SString .+.) <$> parseSchema xs
parseSchema ("Int" :: []) = Just SInt
parseSchema ("Int" :: xs) = (SInt .+.) <$> parseSchema xs
parseSchema ("Char" :: []) = Just SChar
parseSchema ("Char" :: xs) = (SChar .+.) <$> parseSchema xs
parseSchema _ = Nothing

parseCommand : (schema : Schema) ->
               (cmd : String) ->
               (args : String) ->
               Maybe (Command schema)
parseCommand schema "schema" str = SetSchema <$> parseSchema (words str)
parseCommand schema "add" str = Add <$> parseBySchema schema str
parseCommand schema "get" "" = Just All
parseCommand schema "get" val = case all isDigit (unpack val) of
                                     False => Nothing
                                     True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input =
  case span (/= ' ') input of
       (cmd, args) => parseCommand schema cmd (ltrim args)

processCommand : (store : DataStore) ->
                 (cmd : Command (schema store)) ->
                 Maybe (String, DataStore)
processCommand store (SetSchema newschema) =
  case setSchema store newschema of
    Nothing => Just ("Can't update schema\n", store)
    Just store' => Just ("OK\n", store')
processCommand store (Add item) =
  Just ("ID " ++ show (size store) ++ "\n",
        addToStore store item)
processCommand store (Get val) = getEntry val store
processCommand store All = Just (printStore store, store)
processCommand store Quit = Nothing


processInput : (store : DataStore) -> String -> Maybe (String, DataStore)
processInput store inp =
  case parse (schema store) inp of
       Nothing => Just ("Invalid command\n", store)
       (Just cmd) => processCommand store cmd

{-

searchEntry : (query : String) -> (store : DataStore) ->  Maybe (String, DataStore)
searchEntry "" store = Just ("Empty query\n", store)
searchEntry query store
  = case findItem query 0 (items store) of
         Nothing => Just ("Not found\n", store)
         Just (index, str) => Just ((show index)++": "++str++"\n", store)
  where
    findItem : String -> Nat -> Vect n String -> Maybe (Nat, String)
    findItem query index [] = Nothing
    findItem query index (item :: items)
      = case isInfixOf query item of
             False => findItem query (S index) items
             True => Just (index, item)
-}


main : IO ()
main = replWith (MkData SInt _ []) "Command: " processInput
