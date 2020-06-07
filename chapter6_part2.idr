module Main
import Debug.Trace
import Data.Vect;
import Data.String
import Control.IOExcept

%default total

record DataStore (schema : Type) where 
    constructor MkData
    size: Nat
    items: Vect size schema

data DataStoreState a = NotInited | Inited (DataStore a)

data Command = Add String
    | Get Integer
    | Schema (List Type)
    | Quit

addToStore : DataStore a -> a -> DataStore a
addToStore (MkData size items') newitem = MkData _ (addToData items')
    where
    addToData : Vect old a -> Vect (S old) a
    addToData [] = [newitem]
    addToData (item :: items') = item :: addToData items'


replMain : DataStoreState String -> String -> Maybe (String, DataStoreState String)    
replMain ds text = 
    let maybeCommand = parseCommand text 
    in case maybeCommand of 
        Nothing => pure ("Unknown command", ds)
        Just command => processCommand command ds
    where 
        parseType : String -> Maybe Type 
        parseType "string" = pure String
        parseType "int" = pure Int
        parseType _ = Nothing
        
        parseCommand : String -> Maybe Command
        parseCommand text = 
            case span (/= ' ') (trace text (toLower text)) of
                ("add", args) => pure $ Add (ltrim args)
                ("get", args) => Get <$> parseInteger args 
                ("schema", args) => Schema <$> traverse parseType (split (== ' ') (ltrim args))
                ("quit", _) => pure (trace "quitting" Quit)
                _ => Nothing

        partial processCommand : Command -> DataStoreState String -> Maybe (String, DataStoreState String)
        processCommand (Add s) (Inited ds) = 
            let newStore = addToStore ds s
                stringIndex : String = cast (size ds)
            in pure ("ID " ++ stringIndex, Inited newStore)
        processCommand (Get i) (Inited ds) = 
            let maybeValue = do 
                    fin <- integerToFin i (Main.DataStore.size ds)
                    pure $ Data.Vect.index fin (items ds)

                textToShow = fromMaybe "Out of range" maybeValue
            in pure (textToShow, Inited ds)
        processCommand Schema _ = pure (trace "schema" ("schema accepted", Inited (MkData 0 [])))
        processCommand Quit _ = trace "quitting2" Nothing


covering main : IO ()
main = replWith NotInited ("\nCommand:") replMain