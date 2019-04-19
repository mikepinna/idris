module Main

import Data.Vect
import Data.Fin

-- Section 1.  Define bit masks allowing us to pull out the groups of cells in a board that need to contain no overlaps.

||| A proof that some element is found in a vector exactly n times
data ElemExact : Nat -> a -> Vect k a -> Type where
    ElemExactBase : ElemExact 0 x []
    ElemExactHere : ElemExact n x xs -> ElemExact (S n) x (x::xs)
    ElemExactThere : Not (x=y) -> ElemExact n x xs -> ElemExact n x (y::xs)

BitMask : Nat -> Nat -> Type
BitMask k n = (m : Vect k Bool ** ElemExact n True m)

emptyBitMask : BitMask 0 0
emptyBitMask = (_ ** ElemExactBase)

reverseBitMask : BitMask a p -> BitMask a p
reverseBitMask bm = reverseBitMask' emptyBitMask bm where
    reverseBitMask' : BitMask a p -> BitMask b q -> BitMask (a+b) (p+q)
    reverseBitMask' acc (_ ** ElemExactBase) =
        fix acc where
            fix : BitMask a p -> BitMask (a+0) (p+0)
            fix {a} {p} bm = rewrite plusZeroRightNeutral a in rewrite plusZeroRightNeutral p in bm
    reverseBitMask' (_ ** prf1) (_ ** ElemExactHere prf2) =
        fix $ reverseBitMask' (_ ** ElemExactHere prf1) (_ ** prf2) where
            fix : BitMask ((S a) + len) ((S p) + n) -> BitMask (a + (S len)) (p + (S n))
            fix {len} {a} {p} {n} bm = rewrite sym $ plusSuccRightSucc a len in rewrite sym $ plusSuccRightSucc p n in bm
    reverseBitMask' (_ ** prf1) (_ ** ElemExactThere prf2a prf2b) =
        fix $ reverseBitMask' (_ ** ElemExactThere prf2a prf1) (_ ** prf2b) where
            fix : BitMask ((S a) + len) (p + q) -> BitMask (a + (S len)) (p + q)
            fix {a} {len} bm = rewrite sym $ plusSuccRightSucc a len in bm
         
total
applyMask : Vect k a -> BitMask k n -> Vect n a
applyMask [] ([] ** ElemExactBase) = []
applyMask (v::vs) (_ ** ElemExactHere x) = v :: applyMask vs (_ ** x)
applyMask (_::vs) (_ ** ElemExactThere _ x) = applyMask vs (_ ** x)

(++) : BitMask a p -> BitMask b q -> BitMask (a+b) (p+q)
(++) bm1 bm2 = pluss (reverseBitMask bm1) bm2 where
    pluss : BitMask a p -> BitMask b q -> BitMask (a+b) (p+q)
    pluss (_ ** ElemExactBase) bm2 = bm2
    pluss (_ ** ElemExactHere prf1) (_ ** prf2) =
        fix $ pluss (_ ** prf1) (_ ** ElemExactHere prf2) where
            fix : BitMask (len + (S b)) (n + (S q)) -> BitMask (S (len + b)) (S (n + q))
            fix {len} {b} {n} {q} x = rewrite plusSuccRightSucc len b in rewrite plusSuccRightSucc n q in x
    pluss (_ ** ElemExactThere prf1a prf1b) (_ ** prf2) =
        fix $ pluss (_ ** prf1b) (_ ** ElemExactThere prf1a prf2) where
            fix : BitMask (len + (S b)) (p + q) -> BitMask (S (len + b)) (p + q)
            fix {len} {b} x = rewrite plusSuccRightSucc len b in x 
 
(*) : BitMask a p -> (n : Nat) -> BitMask (n*a) (n*p)
(*) x Z = emptyBitMask
(*) x (S k) = x ++ (x * k)



sliceMasks : Vect 27 (BitMask 81 9)
sliceMasks =
    [
        -- verticals
        ((f1 * 0) ++ t1 ++ (f1 * 8)) * 9,
        ((f1 * 1) ++ t1 ++ (f1 * 7)) * 9,
        ((f1 * 2) ++ t1 ++ (f1 * 6)) * 9,
        ((f1 * 3) ++ t1 ++ (f1 * 5)) * 9,
        ((f1 * 4) ++ t1 ++ (f1 * 4)) * 9,
        ((f1 * 5) ++ t1 ++ (f1 * 3)) * 9,
        ((f1 * 6) ++ t1 ++ (f1 * 2)) * 9,
        ((f1 * 7) ++ t1 ++ (f1 * 1)) * 9,
        ((f1 * 8) ++ t1 ++ (f1 * 0)) * 9,

        -- horizontals
        (f9 * 0) ++ t9 ++ (f9 * 8),
        (f9 * 1) ++ t9 ++ (f9 * 7),
        (f9 * 2) ++ t9 ++ (f9 * 6),
        (f9 * 3) ++ t9 ++ (f9 * 5),
        (f9 * 4) ++ t9 ++ (f9 * 4),
        (f9 * 5) ++ t9 ++ (f9 * 3),
        (f9 * 6) ++ t9 ++ (f9 * 2),
        (f9 * 7) ++ t9 ++ (f9 * 1),
        (f9 * 8) ++ t9 ++ (f9 * 0),

        -- boxes
        (t3f6   * 3) ++ (f9 * 6),
        (f3t3t3 * 3) ++ (f9 * 6),
        (f6t3   * 3) ++ (f9 * 6),
        (f9 * 3) ++ (t3f6   * 3) ++ (f9 * 3),
        (f9 * 3) ++ (f3t3t3 * 3) ++ (f9 * 3),
        (f9 * 3) ++ (f6t3   * 3) ++ (f9 * 3),
        (f9 * 6) ++ (t3f6   * 3),
        (f9 * 6) ++ (f3t3t3 * 3),
        (f9 * 6) ++ (f6t3   * 3)
    ]
    where
        t1 : BitMask 1 1
        t1 = (_ ** ElemExactHere ElemExactBase)
        f1 : BitMask 1 0
        f1 = (_ ** (ElemExactThere absurd ElemExactBase))
        t3 : BitMask 3 3
        t3 = t1 * 3
        f3 : BitMask 3 0
        f3 = f1 * 3
        f9 : BitMask 9 0
        f9 = f1 * 9
        t9 : BitMask 9 9
        t9 = t1 * 9
        t3f6 : BitMask 9 3
        t3f6 = (t1 * 3) ++ (f1 * 6)
        f3t3t3 : BitMask 9 3
        f3t3t3 = (f1 * 3) ++ (t1 * 3) ++ (f1 * 3)
        f6t3 : BitMask 9 3
        f6t3 = (f1 * 6) ++ (t1 * 3)

-- Section 2.  Round-trip boards via strings.

columnSeparator : String
columnSeparator = "|"

newline : String
newline = singleton '\n'

groupSeparator : String
groupSeparator = "+---+---+---+" ++ newline

split3 : {n : Nat} -> Vect (n + (n + n)) e -> Vect 3 (Vect n e)
split3 {n} xs =
    let (v1, rest) = splitAt n xs in
    let (v2, v3) = splitAt n rest in
    [v1,v2,v3]
    
showGrp : Show a => Vect 3 a -> String
showGrp grp =
    case map show grp of
        [a,b,c] => a ++ b ++ c

showRow : Show a => Vect 9 a -> String
showRow row =
    case map showGrp $ split3 $ row of
        [a,b,c] => columnSeparator ++ a ++ columnSeparator ++ b ++ columnSeparator ++ c ++ columnSeparator ++ newline

show3Rows : Show a => Vect 27 a -> String
show3Rows rows = 
    case map showRow $ split3 $ rows of
        [a,b,c] => a ++ b ++ c

show9Rows : Show a => Vect 81 a -> String
show9Rows rows =
    case map show3Rows $ split3 $ rows of
        [a,b,c] => groupSeparator ++ a ++ groupSeparator ++ b ++ groupSeparator ++ c ++ groupSeparator

Cell : Type
Cell = Fin 9

data NonEmptyCell = Value Cell | Empty

Board : Type
Board = Vect 81 NonEmptyCell

-- map 0-8 back to '1'-'9'
Show Cell where
    show n = show $ 1 + finToInteger n

Show NonEmptyCell where
    show Empty = " "
    show (Value v) = show v

showBoard : Board -> String
showBoard b = show9Rows b

-- map '1'-'9' to 0-8
parseCharAsNat : Char -> Maybe Nat
parseCharAsNat c =
    if (c > '0' && c <= '9')
    then Just (cast ((ord c) - (ord '1')))
    else Nothing

parseCharAsNonEmptyCell : Char -> Maybe NonEmptyCell
parseCharAsNonEmptyCell ' ' = Just Empty
parseCharAsNonEmptyCell a =
    do
        n <- parseCharAsNat a
        f <- natToFin n 9
        pure $ Value f

parseStringAsBoard : String -> Maybe Board
parseStringAsBoard s =
    let cells = catMaybes $ map parseCharAsNonEmptyCell $ unpack s in
    case decEq (length cells) 81 of
        Yes prf => Just $ rewrite sym prf in fromList cells
        No _ => Nothing
  
-- Section 3.  Pull it together with validity checks for boards and a simple brute forcer.

Slice : Type
Slice = Vect 9 NonEmptyCell

getSlices : Board -> Vect 27 Slice
getSlices b = map (applyMask b) sliceMasks

sliceIsValid : Slice -> Bool
sliceIsValid s =
    not $ any (\n => isRepeated n) [0..8] where
        ff : (f : Fin 9) -> NonEmptyCell -> Bool
        ff f (Value c) = f == c
        ff _ Empty = False

        isRepeated : Fin 9 -> Bool
        isRepeated f = let (n ** _) = filter (ff f) s in n > 1

isValid : Board -> Bool
isValid b = all sliceIsValid $ getSlices b 

isEmpty : NonEmptyCell -> Bool
isEmpty (Value x) = False
isEmpty Empty = True

findBy : (c -> Maybe b) -> List c -> Maybe b
findBy _ [] = Nothing
findBy f (x :: xs) =
    case f x of
        Just a => Just a
        Nothing => findBy f xs

bruteForce : Board -> Maybe Board
bruteForce b =
    case isValid b of
        False => Nothing
        True =>
            case findIndex isEmpty b of
                Nothing => Just b
                Just a => findBy (\n => bruteForce $ replaceAt a (Value n) b) [0..8]
    
-- Section 4.  A test case that runs.

testBoardStr : String
testBoardStr = """
+---+---+---+
|  4| 59| 78|
| 8 |  2|3  |
|5  |   | 1 |
+---+---+---+
|6  | 4 | 8 |
|  1|   |7  |
| 7 | 3 |  5|
+---+---+---+
| 5 |   |  9|
|  8|5  | 6 |
|91 |26 |5  |
+---+---+---+
"""

testBoard : Maybe Board
testBoard = parseStringAsBoard testBoardStr

main : IO ()
main =
        case testBoard of
            Nothing => putStrLn "board not parsed"
            Just b =>
                do
                    putStrLn $ showBoard b
                    putStrLn $ case bruteForce b of
                        Nothing => "solver failed"
                        Just s => showBoard s

