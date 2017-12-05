// Minimise   Z   = c*x
// Subject to A$x = b

// You must by hand convert the problem to standard form.
// Recall that an LP is in standard form if:
// => Objective is a minimisation
// => Constraints are linear equalities
// => RHS of every constraint is non-negative
// => All decision variables are non-negative.

// Swaps elements Y and Z in list X.
swap:{tmp:x[y];x[y]:x[z];x[z]:tmp;x}

// Given a matrix of floats, amends all values sufficiently close to 0 with 0
fpe:{((#x);(#*x))#@[rx;&abs[rx:,/x]<0.0001;:;0f]}

// Given an index set I and then number of variables n, generates the indices
// of variables not in I.
nI:{[I;n]1+&~(1+!n)in I}

// Given the tableau, returns the number of variables the LP has.
nVars:{-2+#*x}

// From a tableau get the constraint matrix A
constraints:{{1_-1_x}'1_x}

// From a tableau get the constraint RHS vector b
constraintRHS:{1_last'x}

// From a tableau get the objective function coefficients c
zCoefficients:{-1_1_*x}

// Aligns the whitespace separated columns represented in the lines of TXT,
// then adds pipe separators between the columns.
pipeSpace:{[txt]
  row:0;
  n:#*M:&:'txt=\:" ";
  while[row<n;
    txt:(r#'txt),'((d:max[r]-r)#\:" "),'(r:M@\:row)_'txt;
    M:(row#/:M),'d+'row_/:M;
    row+:1];
  @[;*M;:;"|"]'txt}

// Given a simplex tableau t with index set I, adds column/row labels and
// prints it nicely.
showTableau:{[t;I]
  colLabels:" "/:("BV";,"Z"),("x",/:$1+!nVars t),(,"RHS");
  rowLabels:"Z","x",/:$I;
  withLabels:(,colLabels),(rowLabels,\:" "),'" "/:'$t;
  pipeSpace withLabels}

// Prints whether the current solution in the tableau T is feasible.
isFeasible:{[t]min@~0>1_last't}

// Given a tableau t and index set I, will return the corresponding basic
// solution.
basicSoln:{[t;I]@[(#*{-1_1_x}'t)#0f;-1+I;:;(last'1_t)%sum'1_t@\:I]}

// Gives the objective value for the current tableau T.
objective:{[t]last@*t}

// Given a tableau t, a p∈ I and a q∉ I, perform a pivot on (p, q) such that
// xp leaves the basis and xq enters the basis, returning the resulting
// pivoted tableau.
pivot:{[t;I;pvt]t-*:'t[pIdx]*/:(%:t . pIdx,q)*@[t@\:q:pvt[1];pIdx:1+&pvt[0]=I;:;0f]}

// Given a tableau t, returns a pivot (p;q) found using standard pivoting
// rules.
// - Entering variable: Ensures non-inferiority
// Pick the non-basic column whose corresponding value in the reduced column
// vector is maximal. If there is a tie, pick the column with the lowest
// index. If no beta[i]>0, then the solution cannot improve and is therefore
// optimal - the algorithm terminates.
// - Leaving variable: Ensures feasibility
// Pick the row whose xBar=RHS%(value in pivot column) quotient is minimal. If
// the minimal value for xBar is infinity, then the LP is unbounded and the
// algorithm terminates.
stdPivot:{[t;I]
  q:1+*&zRow=max zRow:-1_1_t[0];
  p:I@*&xBar=min xBar@&0<xBar:(last'c)%(c:1_t)@\:q;
  (p;q)}

// Given index set I and pivot pv=(p;q), returns a new index set such that
// p has been replaced by q.
reindex:{[I;pvt]@[I;&pvt[0]=I;:;pvt 1]}

// For a given tableau t and an index set I, returns a boolean indicating if
// ∀ i∉ I: β[i]≤0.
isOptimal:{[t;I]min@~0<(*t)@nI[I;nVars t]}

// For a tableau t and index set I, returns a boolean indicating if, for all
// non-basic columns, beta>0 and all other coefficients are <= 0.
// Note, that at optimality, all reduced cost vector entries will be zero,
// so no candidate columns will be found, and so the function would return ().
// I prevent this with the $.
isUnbounded:{[t;I]$[isOptimal[t;I];0b;min@min'~0<+nIs:nIs@\:&0<(nIs:t@\:nI[I;nVars t])@0]}

// Given a tableau t and an initial BFS with index set I, performs the simplex
// algorithm using a pivoting rule given choosePivot:{[t;I]...(p;q)}, saving
// data from every iteration into a table, which it then returns.
simplex:{[choosePivot;t;I]
  i:1;
  running:1b;
  iterations:+`iter`opt`unb`t`I`BFS!6#();
  iterations,:`iter`opt`unb`t`I`BFS!(i;isOptimal[t;I];isUnbounded[t;I];t;I;basicSoln[t;I]);
  while[running;
    pvt:choosePivot[t;I];
    t:pivot[t;I;pvt];
    I:reindex[I;pvt];
    iterations,:`iter`opt`unb`t`I`BFS!(i;isOptimal[t;I];isUnbounded[t;I];t;I;basicSoln[t;I]);
    running:0=+/max'iterations`opt`unb;
    i+:1];
  iterations}

stdSimplex:simplex[stdPivot;;]

// Given a dictionary entry from an iterations table, as produced by
// stdSimplex, produces a line of text showing the information for
// the BFS at that vertex on the hull of the feasible region.
showIterBFS:{[iter]
  "BFS = [",(-1_,/($:iter`BFS),\:","),"], with Z = ",$:objective iter`t};

// Given a dictionary entry from an iterations table, as produced by
// stdSimplex, produces an entire formatted block of text for the
// tableau writeup of the solution.
showIter:{[iter]showTableau[iter`t;iter`I],(,showIterBFS iter),,"==="}

reasonForTermination:{[iterations]
  ("Optimiality reached";"Problem is unbounded")@*&last[iterations]`opt`unb}

// Given a table produced for an iteration by stdSimplex, formats it and
// prints it out, giving intermediate values of the objective for the
// traversed BFSs.
showIterations:{[iterations](,/showIter'iterations),,reasonForTermination iterations}

// A BS is degenerate if any basic variables are zero. Degenerate BSs
// have more than one index set corresponding to them.
isDegenerate:{max@0=constraintRHS[x]}

// ===== Finite Termination Theorum =====
// If all BFSs are non-degenerate, then the simplex algorithm with
// standard pivoting rules must terminate after a finite number of
// steps with either an optimal solution or proof that the problem
// is unbounded.

blandsPivot:{[t;I]
  q:1+*&0<-1_1_t[0];
  p:I@*&xBar=min xBar@&0<xBar:(last'c)%(c:1_t)@\:q;
  (p;q)}

blandsSimplex:simplex[blandsPivot;;]

// Example 1: short
A1:3 6#1 200 400 0 0 0 0 3 2 120 0 120 0 1 1 0 50 50f
I1:3 4

// Example 2: longer
A2:4 7#1 1 1 0 0 0 0 0 2 1 1 0 0 11 0 1 3 0 1 0 18 0 1 0 0 0 1 4f
I2:3 4 5

// Example 3: artificial
A3:4 9#1 3 0 1 -1 0 0 0 12 0 1 1 1 0 0 1 0 10 0 2 -1 0 -1 0 0 1 2 0 1 -2 1 0 1 0 0 6f
I3:6 7 5
