module Main
import Debug.Trace
import Data.Vect;
import Data.String
import Control.IOExcept

%default total

VarArgs : Type -> (numargs : Nat) -> Type
VarArgs t Z = t
VarArgs t (S k) = (next : t) -> VarArgs t k

adder : (Num t) => (numargs : Nat) -> VarArgs t (S numargs)
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

data Format = 
      INumber Format
    | FNumber Format  
    | Str Format
    | Ch Format
    | Lit String Format
    | End

PrintfType : Format -> Type
PrintfType (INumber fmt) = (i : Int) -> PrintfType fmt
PrintfType (FNumber fmt) = (f : Double) -> PrintfType fmt
PrintfType (Ch fmt) = (c : Char) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: tail) = INumber (toFormat tail)
toFormat ('%' :: 'f' :: tail) = FNumber (toFormat tail)
toFormat ('%' :: 'c' :: tail) = Ch (toFormat tail)
toFormat ('%' :: 's' :: tail) = Str (toFormat tail)
toFormat (x :: tail) = Lit (cast x) (toFormat tail)

-- reduceFormat : Format -> Format
-- reduceFormat (INumber x) = INumber (reduceFormat x)
-- reduceFormat (Str x) = Str (reduceFormat x)
-- reduceFormat (Lit x (Lit y t)) = reduceFormat (Lit (x ++ y) t)
-- reduceFormat (Lit x y) = Lit x (reduceFormat y)
-- reduceFormat End = End

reduceFormat : Format -> Format
reduceFormat (INumber x) = INumber (reduceFormat x)
reduceFormat (FNumber x) = FNumber (reduceFormat x)
reduceFormat (Ch x) = Ch (reduceFormat x)
reduceFormat (Str x) = Str (reduceFormat x)
reduceFormat (Lit x r) = 
    case reduceFormat r of 
        Lit y t => Lit (x ++ y) t
        other => Lit x other
reduceFormat End = End

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (INumber fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (FNumber fmt) acc = \f => printfFmt fmt (acc ++ show f)
printfFmt (Ch fmt) acc = \c => printfFmt fmt (acc ++ show c)
printfFmt (Str fmt) acc = \str => printfFmt fmt (acc ++ str)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc

printf : (fmt : String) -> PrintfType (reduceFormat (toFormat (unpack fmt)))
printf _ = printfFmt _ ""

Matrix : Nat -> Nat -> Type
Matrix m n = Vect m (Vect n Int)

testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

TupleVect : Nat -> Type -> Type
TupleVect Z _ = ()
TupleVect (S n) ty = (ty, TupleVect n ty)

main : IO ()
main = print $ 10