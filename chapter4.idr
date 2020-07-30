module Main
import Debug.Trace
import Data.Vect;
import Data.String

record DataStore where
    constructor MkData
    size: Nat
    items: Vect size String
data Command = Add String
    | Get Integer
    | Quit

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items') newitem = MkData _ (addToData items')
    where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (item :: items') = item :: addToData items'


replMain : DataStore -> String -> Maybe (String, DataStore)
replMain ds text =
    let maybeCommand = parseCommand text
    in case maybeCommand of
        Nothing => pure ("Unknown command", ds)
        Just command => processCommand command ds
    where
        parseCommand : String -> Maybe Command
        parseCommand text =
            case span (/= ' ') (toLower text) of
                ("add", args) => pure $ Add (ltrim args)
                ("get", args) => Get <$> parseInteger args
                ("quit", _) => pure Quit
                _ => Nothing
        processCommand : Command -> DataStore -> Maybe (String, DataStore)
        processCommand (Add s) ds =
            let newStore = addToStore ds s
                stringIndex : String = cast (size ds)
            in pure ("ID " ++ stringIndex, newStore)
        processCommand (Get i) ds =
            let maybeValue = do
                    fin <- integerToFin i (Main.DataStore.size ds)
                    pure $ Data.Vect.index fin (items ds)

                textToShow = fromMaybe "Out of range" maybeValue
            in pure (textToShow, ds)
        processCommand Quit _ = Nothing


main : IO ()
main = replWith (MkData 0 []) ("\nCommand:") replMain
