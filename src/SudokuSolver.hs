module SudokuSolver where

import TestSudokus

import Control.Monad
import Text.Printf (printf)
import Data.List (intercalate, foldl', groupBy, sort, delete)

main :: IO ()
main = putStr . showSudoku $ solveSudoku sudoku9x9


{-Data types-}
data Cols = Cols Int Int [Col]
  deriving (Show)

data Col = Col Covered Int [Cell]
  deriving (Show)

data Row = Row Int (Int, Int) [Int]
  deriving (Show)

type Cell = (Covered, Int)

data Covered = C | U
  deriving (Eq, Show)

-- Solve a sudoku, transforming it into an exact cover problem.
-- Implemented using the (DL)X algorithm from Donald Knuth, but without using dancing links,
-- as there are no pointers in pure haskell.
solveSudoku :: [[Int]] -> [[Int]]
solveSudoku []   = []
solveSudoku [[]] = []
solveSudoku xss
  | h /= w         = []                 -- height and weight must be equal
  | sqrH*sqrH /= h = []                 -- the sudoku must be divisible into squares, which are sqrt(sudoku_length) wide
  | length filledSquares == h*h = xss   -- sudoku already solved
  | otherwise = convertSolutionsToSudoku $ solveCoverProblem filledSquares $ convertSudokuToCoverMatrix xss
  where h = length xss
        w = length $ head xss
        sqrH = intRoot h

        filledSquares :: [(Int,Int,Int)]
        filledSquares = getFilledSquares 1 1 xss []
          where getFilledSquares :: Int -> Int -> [[Int]] -> [(Int,Int,Int)] -> [(Int,Int,Int)]
                getFilledSquares _ _ [] coord = coord
                getFilledSquares r c (xs:xss) coord = searchInRow r c xs [] ++ getFilledSquares (r+1) c xss coord
                  where searchInRow _ _ [] coord' = coord'
                        searchInRow r c (x:xs) coord'
                          | x == 0    = searchInRow r (c+1) xs coord'
                          | otherwise = (x,r,c):coord' ++ searchInRow r (c+1) xs coord'


convertSolutionsToSudoku :: [Row] -> [[Int]]
convertSolutionsToSudoku [] = []
convertSolutionsToSudoku rs = map (map scrapCoordinates)
                              . groupBy sameRow
                              . sort
                              $ map scrapCols rs
  where scrapCols (Row n (r,c) cs) = [r,c,n]
        sameRow x y = head x == head y
        scrapCoordinates [r,c,n] = n


solveCoverProblem :: [(Int,Int,Int)] -> (Cols, [Row]) -> [Row]
solveCoverProblem prefilled (cs, rs)
  | null coverProblemSolution = []                          -- sudoku has no solution
  | otherwise = prefilledSolutions ++ coverProblemSolution  -- add prefilled squares to the obtained solution
  where coverProblemSolution = knuthAlg newCoverMatrix rs False [] [] []
        prefilledSolutions = fst rowsAndColsToCover

        rowsAndColsToCover = getPrefilledRowsAndCols
        colsToCover = foldr (++) [] (snd rowsAndColsToCover)
        newCoverMatrix = updateCols $ foldl' (`cover` rs) cs colsToCover

        getPrefilledRowsAndCols = getRC rs prefilled ([],[])
          where getRC [] _ results = results
                getRC _ [] results = results
                getRC (row@(Row n (i,j) col):rs) pref res@(rows,cols) =
                  let prefWithoutNIJ = delete (n,i,j) pref
                  in if length prefWithoutNIJ == length pref
                     then getRC rs pref res
                     else getRC rs prefWithoutNIJ (row:rows,col:cols)


convertSudokuToCoverMatrix :: [[Int]] -> (Cols, [Row])
convertSudokuToCoverMatrix xss = (generateCols, generateRows)
  where l = length xss
        sqrL = intRoot l
        lSq = l*l
        lTr = lSq*l

        invIndices :: [[Int]]
        invIndices = zipWith (:) (cycle doubleNums)
                   $ zipWith (:) (cycle invLSqTo0)
                   $ zipWith (:) [lTr-1,lTr-2..0] tripleLoop
          where invLto0 = [l-1,l-2..0]
                invLSqTo0 = [lSq-1,lSq-2..0]
                tripleLoop = [[i, j, k] | i <- invLto0, j <- invLto0, k <- invLto0]
                doubleNums = invLSqTo0 >>= replicate l

        generateCols :: Cols
        generateCols = Cols (4*lSq) 0 $ map (Col U l) . splitIntoGroups l $ join generateColCells
          where generateColCells = foldl' (\[c1,c2,c3,c4] [i,j,k,m,n,p] -> 
                                     [(U, l*i + p) : c1,
                                      (U, k`div`lSq * lSq + n + p*l) : c2,
                                      (U, i + p*lSq) : c3,
                                      (U, m`div`sqrL * sqrL*lSq + m`mod`sqrL * sqrL*l + p`div`sqrL * lSq + p`mod`sqrL * l + n) : c4
                                     ])
                                   [[],[],[],[]] invIndices
                splitIntoGroups :: Int -> [a] -> [[a]]
                splitIntoGroups l [] = []
                splitIntoGroups l xs = take l xs : splitIntoGroups l (drop l xs)

        generateRows :: [Row]
        generateRows = foldl' (\rows [i,j,k,m,n,p] ->
                                Row (p+1) (m+1,n+1) [i,
                                                     lSq + m*l + p,
                                                     2*lSq + j,
                                                     3*lSq + m`div`sqrL * sqrL*l + n`div`sqrL * l + p
                                                    ] : rows) [] invIndices


knuthAlg :: Cols -> [Row] -> Bool -> [Int] -> [[Int]] -> [Row] -> [Row]
knuthAlg cs rs backtrack cStack rStack solutions
  | colsEmpty cs        = solutions               -- all columns covered -> the found partial solutions are the solutions to the problem
  | colSize minCol == 0 = if null rStack then []  -- problem unsolvable from the beginning
                          else knuthAlg (uncoverColumns $ colsToCoUncover $ head $ head rStack)
                                        rs True
                                        cStack rStack
                                        (tail solutions)
  | backtrack = let r = filter (\row -> row `notElem` head rStack) $ getColUncoveredRows $ getCol cs $ head cStack
                in if null r                    -- no more solutions for this constraint
                    then if length cStack == 1  -- already backtracked back to the first level
                         then []                           -- no solution
                         else let newRStack = tail rStack  -- backtrack further
                               in knuthAlg (uncoverColumns $ colsToCoUncover $ head $ head newRStack)
                                           rs True
                                           (tail cStack) newRStack
                                           (tail solutions)
                    else let newSolutionRowInd = head r
                         in knuthAlg (coverColumns $ colsToCoUncover newSolutionRowInd)
                                     rs False
                                     cStack (consToHeadOfList newSolutionRowInd rStack)
                                     ((rs !! newSolutionRowInd) : solutions)
  | otherwise = let newSolutionRowInd = head $ getColUncoveredRows minCol
                in knuthAlg (coverColumns $ colsToCoUncover newSolutionRowInd)
                            rs False
                            (minColIndex:cStack) ([newSolutionRowInd]:rStack)
                            ((rs !! newSolutionRowInd) : solutions)
  where
    minColIndex = getColsMinIndex cs
    minCol = getCol cs minColIndex

    colsToCoUncover :: Int -> [Int]
    colsToCoUncover = getColsFromRow rs

    coverColumns :: [Int] -> Cols
    coverColumns = updateCols . foldl' (`cover` rs) cs

    uncoverColumns :: [Int] -> Cols
    uncoverColumns = updateCols . foldl' (`uncover` rs) cs

    consToHeadOfList :: Int -> [[Int]] -> [[Int]]
    consToHeadOfList i (xs:xss) = (i:xs):xss


{- Cover functions -}
modifyCol :: Cols -> Int -> (Col -> Col) -> Cols
modifyCol (Cols n min cols) i f = Cols n min (modify' cols 0)
  where modify' (c:cls) k
          | k == i    = f c : cls
          | otherwise = c:modify' cls (k+1)

cover :: Cols -> [Row] -> Int -> Cols
cover = coUncover coverColHeader coverRowInCol

uncover :: Cols -> [Row] -> Int -> Cols
uncover = coUncover uncoverColHeader uncoverRowInCol

coUncover :: (Cols -> Int -> Cols) -> (Cols -> Int -> Int -> Cols) -> Cols -> [Row] -> Int -> Cols
coUncover fCoUncoverHeader fCoUncoverRow cols rows cInd = coUncoverRows $ fCoUncoverHeader cols cInd
  where
    rowsToCover = getColUncoveredRows $ getCol cols cInd
    colsToCover rInd = filter (/= cInd) $ getColsFromRow rows rInd
    rcPairs = concatMap (\r -> zip (repeat r) (colsToCover r)) rowsToCover
    coUncoverRows cc = foldl' (\colsAcc (r,c) -> fCoUncoverRow colsAcc c r) cc rcPairs

coverColHeader :: Cols -> Int -> Cols
coverColHeader = coUncoverColHeader C decrCols

uncoverColHeader :: Cols -> Int -> Cols
uncoverColHeader = coUncoverColHeader U incrCols

coUncoverColHeader :: Covered -> (Cols -> Cols) -> Cols -> Int -> Cols
coUncoverColHeader coUncovered deIncr cols i =
  deIncr $ modifyCol cols i (\(Col _ n cls) -> Col coUncovered n cls)

coverRowInCol :: Cols -> Int -> Int -> Cols
coverRowInCol = coUncoverRowInCol C

uncoverRowInCol :: Cols -> Int -> Int -> Cols
uncoverRowInCol = coUncoverRowInCol U

coUncoverRowInCol :: Covered -> Cols -> Int -> Int -> Cols
coUncoverRowInCol coUncover cols cInd rInd = modifyCol cols cInd coverRow
  where coverRow = \(Col cov n cls) ->
                   Col cov n $
                   map (\(cv,r) -> if r == rInd then (coUncover,r) else (cv,r)) cls


{- Functions for Cols, Col, Row -}
colsEmpty :: Cols -> Bool
colsEmpty (Cols n _ _) = n == 0

decrCols :: Cols -> Cols
decrCols (Cols n min cs) = Cols (n-1) min cs

incrCols :: Cols -> Cols
incrCols (Cols n min cs) = Cols (n+1) min cs

updateCols :: Cols -> Cols
updateCols (Cols n _ cs) = Cols n newMin updatedCS
  where updatedCS = updateColSizes cs
        newMin = getMinIndex updatedCS

updateColSizes :: [Col] -> [Col]
updateColSizes cs = map (\c@(Col cov _ cls) ->
                      if cov == C
                      then c
                      else Col cov (countUncoveredCells cls) cls) cs

getCol :: Cols -> Int -> Col
getCol (Cols _ _ cs) i = cs !! i

getColsMinIndex :: Cols -> Int
getColsMinIndex (Cols _ min cs) = min

getMinIndex :: [Col] -> Int
getMinIndex cs = findMin 0 0 (maxBound::Int) cs
  where findMin _ iMin _ []                  = iMin
        findMin i iMin nMin ((Col C _ _):cs) = findMin (i+1) iMin nMin cs  -- ignore the covered columns
        findMin i iMin nMin (c:cs)           = findMin (i+1) iMin' nMin' cs
          where n     = colSize c
                iMin' = if n < nMin then i else iMin
                nMin' = min n nMin

getAllColRows :: Col -> [Int]
getAllColRows (Col _ _ cs) = map snd cs

getColUncoveredRows :: Col -> [Int]
getColUncoveredRows (Col _ _ cs) = [r | (c,r) <- cs, c == U]

countUncoveredCells :: [Cell] -> Int
countUncoveredCells cls = length $ filter (\(c,r) -> c == U) cls

colSize :: Col -> Int
colSize (Col _ n _) = n

getColsFromRow :: [Row] -> Int -> [Int]
getColsFromRow rows i = getColsList $ rows !! i
  where getColsList (Row n (x,y) cs) = cs

intRoot :: Int -> Int
intRoot = floor . sqrt . fromIntegral

-- Utility method to show a sudoku
-- show sudoku with
-- >>> putStr (showSudoku sudoku)
showSudoku :: [[Int]] -> String
showSudoku xss = unlines $ intercalate [showDivider] $ chunksOf squareSize $ map showRow xss
  where
    size = length xss
    squareSize = intRoot size 
    numberSize = size `div` 10 + 1

    showRowSection xs = unwords $ map (printf ("%0" ++ show numberSize ++ "d")) xs
    showRow xs = intercalate "|" $ map showRowSection $ chunksOf squareSize xs
    showDivider = intercalate "+" $ replicate squareSize $ replicate ((numberSize + 1) * squareSize - 1) '-'

    chunksOf :: Int -> [e] -> [[e]]
    chunksOf i [] = []
    chunksOf i ls = take i ls : chunksOf i (drop i ls)
