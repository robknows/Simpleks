# Simpleks - Simplex in K

- Educational tool for verbosely solving linear programs using the simplex
method.

- Not simply a hack of matrix operations. Uses an index set, which is 1-based
and visually formats simplex solutions using the tableau format including
labels for rows and columns.

- Allows you to inspect every iteration of the algorithm.

## Usage

- You must create the tableau by hand and then enter it as a matrix which
includes the objective value as a column of the matrix.

- If doing two-phase simplex, you have to insert the artificial variables
manually, and then once you've solved it you must then manually convert back
to the original LP.

## Functionality

- Standard pivoting rules

- Bland's pivoting rules

- Simplex iteration with per-iteration data of the BFS represented at that
iteration, the tableau and the index set.

- Gives the way in which the algorithm terminates - either optimal or
unbounded.

## Next up - Annotated integer programming methods

- Gomory cuts

- Knapsack cover cuts

- Branch and bound
