# Sudoku Solver
This solver uses the exact cover problem approach to solve a given sudoku.

It will solve any sudoku, which has a side equal to n*n, where n >= 2. For example 4x4, 9x9, 16x16, ...


At the moment if you execute `stack run` it will just output the solution to the sudoku `sudoku9x9` from the file `TestSudokus.hs`.

To solve your own sudokus, load it with `ghci` and pass an `[[Int]]` with your unsolved sudoku to the function `solveSudoku`. An empty square is marked with a `0`. For example:

`> solveSudoku [[2,4,0,0],[1,1,0,0],[0,3,0,0],[0,0,1,4]]`

For a nicer output, you can use:

`> putStr . showSudoku $ solveSudoku [[2,4,0,0],[1,1,0,0],[0,3,0,0],[0,0,1,4]]`
