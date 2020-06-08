module Main
import Debug.Trace
import Data.Vect;
import Data.String
import Control.IOExcept

%default total

infixr 5 .+.

data Schema = SString | SInt | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where 
    constructor MkData
    schema : Schema
    size: Nat
    items: Vect size (SchemaType schema)


addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items') newitem = MkData schema _ (addToData items')
    where
    addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    addToData [] = [newitem]
    addToData (item :: items') = item :: addToData items'


data Command : Schema -> Type where
    Add : SchemaType schema -> Command schema
    Get : Integer -> Command schema
    Quit : Command schema   

processCommand : (Command schema) -> DataStore -> Maybe (String, DataStore)
processCommand (Add s) ds = 
    let newStore = addToStore ds s
        stringIndex : String = show (size ds)
    in pure ("ID " ++ stringIndex ++ "\n", newStore)    
processCommand (Get i) ds = 
    let maybeValue = do 
            fin <- integerToFin i (Main.DataStore.size ds)
            pure $ ?display $ Data.Vect.index fin (items ds)

        textToShow = fromMaybe "Out of range" maybeValue
    in pure (textToShow, ds)
processCommand Quit _ = Nothing

-- replMain : DataStore -> String -> Maybe (String, DataStore)    
-- replMain ds text = 
--     let maybeCommand = parseCommand text 
--     in case maybeCommand of 
--         Nothing => pure ("Unknown command", ds)
--         Just command => processCommand command ds
--     where 
--         parseCommand : String -> Maybe Command
--         parseCommand text = 
--             case span (/= ' ') (toLower text) of
--                 ("add", args) => pure $ Add (ltrim args)
--                 ("get", args) => Get <$> parseInteger args 
--                 ("quit", _) => pure Quit
--                 _ => Nothing
--         processCommand : Command -> DataStore -> Maybe (String, DataStore)
--         processCommand (Add s) ds = 
--             let newStore = addToStore ds s
--                 stringIndex : String = cast (size ds)
--             in pure ("ID " ++ stringIndex, newStore)
--         processCommand (Get i) ds = 
--             let maybeValue = do 
--                     fin <- integerToFin i (Main.DataStore.size ds)
--                     pure $ Data.Vect.index fin (items ds)

--                 textToShow = fromMaybe "Out of range" maybeValue
--             in pure (textToShow, ds)
--         processCommand Quit _ = Nothing


-- main : IO ()
-- main = replWith (MkData 0 []) ("\nCommand:") replMain