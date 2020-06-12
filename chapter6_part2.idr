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

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = 
    let (openQuote, rest) = span (== '"') input
        (text, rest') = span (/= '"') rest
        (closeQuote, rest'') = span (== '"') rest'
    in case (openQuote, closeQuote) of 
        ("\"", "\"") => pure (text, ltrim rest'')
        _ => Nothing
parsePrefix SInt input = 
    let (digits, rest) = span isDigit input
    in (\i => (i, ltrim rest)) <$> parseInteger digits
parsePrefix (x .+. y) input = do 
    (rx, rest) <- parsePrefix x input
    (ry, rest') <- parsePrefix y rest 
    pure ((rx, ry), rest')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = do
    (res, tail) <- parsePrefix schema input
    if tail == "" then pure res else Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" rest = Add <$> parseBySchema schema rest
parseCommand schema "get" rest = Get <$> parseInteger rest
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = 
    let (cmd, args) = span (/= ' ') input
    in parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ ", " ++ display itemr

processCommand : (ds : DataStore) -> (Command (schema ds)) -> Maybe (String, DataStore)
processCommand ds (Add s) = 
    let newStore = addToStore ds s
        stringIndex : String = show (size ds)
    in pure ("ID " ++ stringIndex ++ "\n", newStore)    
processCommand ds (Get i) = 
    let maybeValue = do 
            fin <- integerToFin i (Main.DataStore.size ds)
            pure $ display $ Data.Vect.index fin (items ds)

        textToShow = fromMaybe "Out of range" maybeValue
    in pure (textToShow, ds)
processCommand _ Quit = Nothing


replMain : DataStore -> String -> Maybe (String, DataStore)    
replMain ds text = 
    let maybeCommand = parse (schema ds) text
    in case maybeCommand of
        Nothing => pure ("Unknown command", ds)
        Just command => processCommand ds command


partial main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) ("\nCommand:") replMain