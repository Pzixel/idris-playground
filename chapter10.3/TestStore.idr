import DataStore

testStore : DataStore (SString .+. SString .+. SInt)
testStore =
    addToStore ("Mercury", "Mariner 10", 1974) (
        addToStore ("Venus", "Venera", 1961) (
            addToStore ("Uranus", "Voyager 2", 1986)(
                addToStore ("Pluto", "New Horizons", 2015)
                empty
            )
        )
    )

listItems : DataStore schema -> List (SchemaType schema)
listItems input with (storeView input)
    listItems empty | SNil = []
    listItems (addToStore value store) | (SAdd rec) = value :: listItems store | rec

getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues input with (storeView input)
    getValues empty | SNil = []
    getValues (addToStore (MkPair _ value) store) | (SAdd rec) = value :: listItems store | rec
