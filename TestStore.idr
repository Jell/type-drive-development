import DataStore

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974) $
            addToStore ("Venus", "Venera", 1961) $
            addToStore ("Uranus", "Voyager 2", 1986) $
            addToStore ("Pluto", "New Horizons", 2015) $
            empty

listItems : DataStore schema -> List (SchemaType schema)
listItems input with (storeView input)
  listItems input | SNil = []
  listItems (addToStore value store) | (SAdd rec)
    = value :: listItems store | rec

filterKeys : (test : SchemaType val_schema -> Bool) ->
             DataStore (SString .+. val_schema) ->
             List String
filterKeys test input with (storeView input)
  filterKeys test x | SNil = []
  filterKeys test (addToStore (key, value) store) | (SAdd rec)
    = let rest = filterKeys test store | rec in
      if test value then key :: rest else rest

getValues : DataStore (SString .+. val_schema) ->
            List (SchemaType val_schema)
getValues input with (storeView input)
  getValues input | SNil = []
  getValues (addToStore (_, value) store) | (SAdd rec)
    = value :: (getValues store | rec)


testStore2 : DataStore (SString .+. SInt)
testStore2 = addToStore ("First", 1) $
             addToStore ("Second", 2) $
             empty
