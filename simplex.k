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

// Given constraints A,b, objective c, and index set I: produces a tableau.
tableau:{[A;b;c;I]
  B:A@\:bI:-1+I;
  N:A@\:notI:nI[I;#c];
  cB:c@bI;
  cN:c@notI;
  r:cN-(+N)$(+!B)$cB;
  bs:(!B)$b;
  Z:sum cB*bs;
  nB:#I;
  zRow:"f"$,/1,(nB#0),(-:r),Z;
  id:"f"$0=(2#nB)#!1+nB;
  cRows:"f"$(nB#0),'id,'((!B)$N),'(!B)$b;
  allRows:fpe (,zRow),cRows;
  swap[;1+!#I;I]'allRows}

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
  colLabels:" "/:("BV";,"Z"),("x",/:$1+!-2+#*t),(,"RHS");
  rowLabels:"Z","x",/:$I;
  withLabels:(,colLabels),(rowLabels,\:" "),'" "/:'$t;
  pipeSpace withLabels}

// Given the constraints A, b, the index set I and a candidate vector X,
// will print some text containing whether X is in fact a solution to the
// constraints, if it is basic and if it is feasible.
showBFS:{[A;b;I;X]
  isSolution:$[b~+/'A*\:X;"";"non-"],"solution";
  isBasic:$[min 0=X a@&~(a:(!#X)) in -1+I;"";"non-"],"basic";
  isFeasible:$[(8=#isSolution)&min 0<X;"";"in"],"feasible";
  isBasic," ",isFeasible," ",isSolution}

// Given a tableau t and index set I, will return the corresponding basic
// solution.
readBasicSolution:{[t;I]@[(#*{-1_1_x}'t)#0f;-1+I;:;last'1_t]}

// Given a tableau t, a p∈ I and a q∉ I, perform a pivot on (p, q) such that
// xp leaves the basis and xq enters the basis, returning the resulting
// pivoted tableau.
pivot:{[t;p;q]t-t[p]*/:@[t@\:q;p;:;0]}

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
selectPivotStd:{[t]
  q:*&zRow=max zRow:t[0];
  p:1+*&xBar=min xBar:(last'c)%(c:1_t)@\:q;
  (p;q)}

// Given index set I and pivot pv=(p;q), returns a new index set such that
// p has been replaced by q.
reindex:{[I;pv]@[I;&(pv 0)=I;:;pv 1]}

// For a given tableau t and an index set I, returns a boolean indicating if
// ∀ i∉ I: β[i]≤0.
isOptimal:{[t;I]min 0~<(*t)@nI[I;nVars t]}

// For a tableau t and index set I, returns a boolean indicating if, for all
// non-basic columns, beta>0 and all other coefficients are <= 0.
isUnbounded:{[t;I]min@min'~0<+nIs:nIs@\:&0<(nIs:t@\:nI[I;nVars t])@0}

// Given an LP specified by constraints A and b, an objective function
// specified by c and an initial BFS with index set I, performs the one phase
// simplex algorithm using standard pivoting rules.
stdOnePhaseSimplex:{[A;b;c;I]}

// Example 1:
A1:2 8#2 -1 3 2 3 2 1 0 3 4 2 2 3 0 0 1f
b1:4 2f
c1:6 3 4 2 -3 4 0 0f
I1:4 3
t1:tableau[A1;b1;c1;I1]
ta1:showTableau[t1;I1]
bs1:readBasicSolution[t1;I1]
bfs1:showBFS[A1;b1;I1;bs1]

// Example 2:
A2:4 8#1 0 0 0 1 2 1 1 0 1 0 0 1 1 -1 5 0 0 1 0 2 -3 1 3 0 0 0 1 -1 2 -1 -1
I2:1 2 3

// Example 3:
A3:4 7#1 1 1 0 0 0 0 0 2 1 1 0 0 11 0 1 3 0 1 0 18 0 1 0 0 0 1 4
