module Main
import Debug.Trace
import Data.Vect;
import Data.String
import Control.IOExcept

%default total

infixr 5 .+.

data Schema = SChar | SString | SInt | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SChar = Char
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
    SetSchema : (newschema : Schema) -> Command schema
    Add : SchemaType schema -> Command schema
    Get : Integer -> Command schema
    Quit : Command schema   

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SChar input = 
    let (openQuote, rest) = span (== '\'') input
        (text, rest') = span (/= '\'') rest
        (closeQuote, rest'') = span (== '\'') rest'
    in case (openQuote, (unpack text), closeQuote) of 
        ("\'", [char], "\'") => pure (char, ltrim rest'')
        _ => Nothing
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

parseSingleSchema : String -> Maybe Schema
parseSingleSchema "Char" = pure SChar
parseSingleSchema "Int" = pure SInt
parseSingleSchema "String" = pure SString
parseSingleSchema _ = Nothing

combineSchemas : List Schema -> Maybe Schema
combineSchemas [] = Nothing 
combineSchemas (x :: xs) = pure $ foldl (.+.) x xs

parseSchema : String -> Maybe Schema       
parseSchema input = do
    types <- traverse parseSingleSchema (words input)
    combineSchemas types

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "schema" rest = SetSchema <$> parseSchema rest
parseCommand schema "add" rest = Add <$> parseBySchema schema rest
parseCommand schema "get" rest = Get <$> parseInteger rest
parseCommand schema "quit" "" = Just Quit
parseCommand schema "exit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = 
    let (cmd, args) = span (/= ' ') input
    in parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SChar} item = show item
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ ", " ++ display itemr

processCommand : (ds : DataStore) -> (Command (schema ds)) -> Maybe (String, DataStore)
processCommand ds (SetSchema schema) = Just ("Ok", MkData schema _ [])
processCommand ds (Add s) = 
    let newStore = addToStore ds s
        stringIndex : String = show (size ds)
    in pure ("ID " ++ stringIndex, newStore)    
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
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "\nCommand:" replMain