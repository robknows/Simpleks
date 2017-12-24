// For parsing a linear program from a table into standard form so the
// algorithms can be applied.

// Example:
// Jenny and Oliver are making tables and chairs to sell for a charity sale.
// Tables take 3 hours to make, chairs take 2. They have 24 hours.
// Tables require 2 units of wood, chairs require 1. They have 18 units of wood.
// Tables use 2 units of varnish, chairs use 3. They have 42 units of varnish.
// Tables sell for £3, chairs sell for £2.
// They have this data in a table called furniture.
// Using an LP, help them maximise profit.

// Solution:
// Statement of LP:
// Let P = profit; x1 = #tables made; x2 = #chairs made
// max P = 3x1 + 2x2
// s.t
// 2x1 + x2  <= 18
// 2x1 + 3x2 <= 42
// 3x1 + x2  <= 24
// xi >= 0 for all 1<=i<=2

// In standard form:
// Let Z = -P => P* = -Z*
// min Z = -3x1 -2x2
// s.t
// 2x1 + x2  + x3 = 18
// 2x1 + 3x2 + x4 = 42
// 3x1 + x2  + x5 = 24
// xi >= 0 for all 1<=i<=5

// As an initial tableau:
// 1 3 2 0 0 0 0
// 0 2 1 1 0 0 18
// 0 2 3 0 1 0 42
// 0 3 1 0 0 1 24

// Method:
// Parsing:
// Grammar of an LP in EBNF:
// D           =:: [0-9]
// N           =:: (D+ "."?)? D+
// Coefficient =:: N | epsilon
// Idx         =:: [D]+
// LinOp       =:: "+"|"-"
// Term        =:: LinOp Coefficient "x" Idx
// Fx          =:: Term
// Fx          =:: Term LinOp Fx
// Objective   =:: ("min"|"max")("A-W"|"Y"|"Z") = Fx
// Cmp         =:: (">="|"<="|"=")
// Constraint  =:: Fx Cmp N
// LP          =:: Objective "s.t" Constraint* "xi >= 0 for all 1<=i<=" Idx

// Input: list of strings representing rows in a description of an LP

// Parsing Fx: Given nVars and an Fx, returns a list of coefficients
// cs = A list of zeroes with length nVars
// split by spaces -> Term (LinOp Term)*
// With the first word, split by x.
//   Parse the first as a float v. Parse the second as an int i
//   Amend cs at position i-1 with the value v
// cut and flip to get (linop;term) pairs. Concatenate each pair
// perform the operation done on word 1 for every pair.
// Return the now very amended cs as the list of coefficients.

// Parsing Objective: Returns first row of tablaeu
// Split by spaces
// If first word is min, c = 1
// If first word is max, c = -1
// Ignore the second word - it is the name of the objective variable
// The third word is "="
// Join remaining words by " " and parse it as an Fx.
// return (1,c*parsedFx)

// Parsing a constraint: Returns a row of the tableau
// split by spaces, dropping the last two words.
// Parse the remainder as an Fx return (0,parsedFx,lastWord)

// Parsing an entire LP: Returns a simplex-able tableau
// Split the last line by "=". Take the last word and parse it as an int.
//  That + number of constraint rows = number of variables.
//  This can be distilled at the end by checking for all-0 columns.
// Parse the first row as the objective row
// Drop  the next  row, it says only "s.t"
// Parse subsequent rows up to but not including the last as constraint rows
// Concatenate and return.

furnitureCoefficients:([] item:`table`chair;price:3 2f;hours:3 1f;wood:2 1f;varnish:2 3f)
furnitureAvailability:`hours`wood`varnish!24 18 42f
furnitureLP:("max P = 3x1 + 2x2";"s.t";"2x1 + x2 <= 18";"2x1 + 3x2 <= 42";"3x1 + x2 <= 24";"xi >= 0 for all 1<=i<=2")

// Given an Fx X, returns a list containing a 1 list, followed by a (possibly
// empty) list of 2-lists of (LinOp;Term). Casts the first element of each
// list as a float and the second as an int.
linOpTermPairs:{{"FI"$'x}'"x"\:',/'|:|:'.q.cut[2;|:(" "\:x)]}

// Given nVars X and a string Y representing an Fx, parses it into a list of
// coefficients for variables numbered by the value given as X
parseFx:{{@[x;-1+y 1;:;1f^(y 0)]}/[x#0f;linOpTermPairs y]}

// Given nVars X and an objective line Y, produces the objective row of the
// initial tableau.
parseObjective:{1f,(1-2*"max"~(" "\:y))*parseFx[x;" "/:3_(" "\:y)],0f}

// Given nVars X and constraint line Y produces a constraint row of the
// initial tableau.
parseConstraint:{0f,parseFx[x;" "/:-2_ws],"F"$last ws:" "\:y}

// Given a list of strings representing an LP formulation X, creates an
// intermediate result representing the initial tableau with no auxilliary
// variables - no slacks, no artificials.
parseLPNoAux:{
  n:"J"$last@"="\:last x;
  Z:parseObjective[n;x 0];
  constraintLines:(-1)_2_x;
  constraints:parseConstraint[n;]'[constraintLines];
  (,Z),constraints}

// Given LP formulation text X, produces a list of symbols representing the
// constraint operators for each constraint, top to bottom: `lt`eq`gt.
constraintOps:{(("<=";,"=";">=")!(`lt`eq`gt))@*:'-2#/:" "\:'-1_2_x}

// lt constraint => Add slack
// eq constraint => Add artificial
// gt constraint => Add slack and artificial
// For each (row;constraintOp) pair, add the variables to the row, and add
// any artificial variables also to a new objective row, which replaces the
// original objective. Also add 0s for every other row in those positions.

// Given an incomplete tableau T, completes the Ith constraint row (1-based)
// by adding the appropriate auxilliary variables, determined by function F.
// F creates appropriate columns of the tableau, which are inserted before the
// RHS, as you'd expect. F takes the number of columns as x, and the row being
// worked on as y.
// The artificial variable will be basic in the initial auxilliary
// tableau, so it should not appear in the objective row, hence we need also to
// subtract the Ith row from the objective row if an artificial variable is
// added.
addAuxs:{[f;t;i]
  t:(-1_/:t),'f[#t;i],'last't;
  if[1f~t[0;-2+#*t];t[0]-:t i];
  A:1f,1_-:t 0;
  (,A),1_t}

// For an eq constraint
addEqAuxs:addAuxs[{@[x#0f;0,y;:;1f]};;]
// For an lt constraint
addLtAuxs:addAuxs[{@[x#0f;y;:;1f]};;]
// For an gt constraint
addGtAuxs:addAuxs[{@[x#0f;y;:;-1f],'@[x#0f;0,y;:;1f]};;]

// Given a tableau X, replaces the current objective row with an empty row
// containing a 1 as the first, and all the rest 0s.
prepAuxilliaryObjective:{(,1f,(-1+#x)#0f),1_x}

auxApply:{[vals;f;i]f[vals;i]}
// Given an LP formulation X as a list of strings, produces an initial tableau for
// phase one of the 2-phase simplex algorithm.
parsePhaseOne:{
  cons:constraintOps x;
  vals:parseLPNoAux x;
  fs:(`lt`eq`gt!(addLtAuxs;addEqAuxs;addGtAuxs))@cons
  is:1+!#cons;
  auxApply/[prepAuxilliaryObjective vals;fs;is]}

// Given an initial simplex tableau as produced by parseLP, T, finds and
// returns an initial index set, if one exists. If it doesn't, it throws
// 'bfs to signal that this is not a basic feasible solution.
getInitialIndexSet:{[t]
  idxs:idxs@&1=sum'(1_t)@\:idxs:1+&1=#:'&:'"b"$1_+t;
  nBasicVariables:-1+#t;
  if[nBasicVariables>#idxs;'bfs];
  nBasicVariables#idxs}

// For an eq constraint
eqArtificials:{`cnt`avs!(x+1;y,x)}
// For an lt constraint
ltArtificials:{`cnt`avs!(x+1;y)}
// For an gt constraint
gtArtificials:{`cnt`avs!(x+2;y,x+1)}

// Given an LP formulation X, determines the indices of the artificial variables
// generated by the parser by following the phase-one parsing rules.
// lt => +1 slack, +0 artificial
// eq => +0 slack, +1 artificial
// gt => +1 slack, +1 artificial
artificialVariables:{
  nLpVars:{"J"$last@"="\:last x};  
  accAvs:{[d;constraint]((`lt`eq`gt!(ltArtificials;eqArtificials;gtArtificials))@constraint)[d`cnt;d`avs]};
  (accAvs/[`cnt`avs!(1+nLpVars x;());constraintOps x])`avs}

// Given an optimal basis from the completion of phase-one and a list of the
// indices of the artificial variables associated with that auxilliary tableau,
// produces a new index set for use in phase-two.
reindexSet:{[p1I;avs]
  idxAdjustments:#:'=:,/&:'p1I>/:avs;
  @[p1I;!idxAdjustments;-;.:idxAdjustments]}

// Given a tableau and its index set, amends the tableau such that all of the
// basic rows have pivot elements of 1f.
normalisePivotRows:{[t;I]
  amendNormalisedPivotRow:{[t;I;i]
    normalisePivotRow:{[t;I;i](t@i)**:%:pr@&:~:0=pr:1_t@\:I@i-1};
    @[t;i;:;normalisePivotRow[t;I;i]]};
  amendNormalisedPivotRow/[t;(#I)#,I;1+!#I]}

// Given a normalised tableau T and index set I, edits T to ensure that it
// has a basic representation for the objective function, by 'repivoting' on
// each basic rows pivot element.
repivot:{[t;I]
  repivotColumn:{[t;I;i]$[0f=t[0;I@i];t;@[t;0;-;t[0;I@i]*t i+1]]};
  repivotColumn/[t;(#I)#,I;!#I]}

// Given an LP formulation lp as a list of strings, and the last (optimal)
// entry from the simplex iterations table after running the simplex algorithm
// for phase-one:
// This function returns a starting point for phase-two in the form of a
// dictionary with key `tableau`indexSet.
prepPhaseTwo:{[lp;p1Table]
  p1:parsePhaseOne lp;
  optimalT:(optimalP1:last p1Table)`t;
  avs:artificialVariables lp;
  nonArtificialTableau:1_optimalT@\:.q.except[!#*optimalT;avs];
  Z:parseObjective[-2+#*nonArtificialTableau;lp 0];
  I:reindexSet[optimalP1`I;avs];
  unnormalised:(,Z),nonArtificialTableau;
  normalised:normalisePivotRows[unnormalised;I];
  `tableau`indexSet!(repivot[normalised;I];I)}
