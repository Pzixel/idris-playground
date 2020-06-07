module Main
import Debug.Trace
import Data.Vect;
import Data.String
import Control.IOExcept

data VectUnknown : Type -> Type where
    MkVect : (len : Nat) -> Vect len a -> VectUnknown a 

implementation Show a => Show (VectUnknown a) where 
    show (MkVect len vec) = show len ++ " " ++ show vec

whileM' : (Monad m, Monad f, Alternative f) => (a -> Bool) -> m a -> m (f a)
whileM' p f = go
    where go = do
            x <- f
            if p x
                then do
                        xs <- go
                        pure (pure x <|> xs)
                else pure empty

whileM : Monad m => (a -> Bool) -> m a -> m (List a)
whileM = whileM'     

readToBlank : IO (List String)
readToBlank = whileM (/= "") getLine

readVect : IO (len ** Vect len String)
readVect = do 
    list <- readToBlank
    let vec = fromList list
    pure (_ ** vec)

readAndSave : IO ()
readAndSave = do 
  content <- readToBlank
  filename <- getLine 
  Right _ <- writeFile filename (unlines content)
  pure ()

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do 
    Right content <- readFile filename
    let list = lines content
    let vec = fromList list
    pure (_ ** vec)

zipInputs : IO ()
zipInputs =  
    do putStrLn "Enter first vector (blank line to end):"
       (len1 ** vec1) <- readVect
       putStrLn "Enter second vector (blank line to end):"
       (len2 ** vec2) <- readVect
       case exactLength len1 vec2 of
            Nothing => putStrLn "Vectors are different lengths"
            Just vec2' => printLn (zip vec1 vec2')
    
main : IO ()
main = do
    items <- readVect
    print items