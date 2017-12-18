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
// xi >= 0 for all 1<=i<=2.

// In standard form:
// Let Z = -P => P* = -Z*
// min Z = -3x1 -2x2
// s.t
// 2x1 + x2  + x3 = 18
// 2x1 + 3x2 + x4 = 42
// 3x1 + x2  + x5 = 24
// xi >= 0 for all 1<=i<=5.

// As an initial tableau:
// 3 2 0 0 0 0
// 2 1 1 0 0 18
// 2 3 0 1 0 42
// 3 1 0 0 1 24

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
// split by spaces
// dropping the last two words, parse the remainder as an Fx
// return (0,parsedFx,lastWord)

// Parsing an entire LP: Returns a simplex-able tableau
// Split the last line by "=". Take the last word and parse it as an int.
//  That + number of constraint rows = number of variables.
//  This can be distilled at the end by checking for all-0 columns.
// Parse the first row as the objective row
// Drop  the next  row, it says only "s.t"
// Parse subsequent rows up to but not including the last as constraint rows
// Concatenate and return.

furniture:([] item:`table`chair;price:3 2f;hoursRequired:3 1f;woodRequired:2 1f;varnishRequired:2 3f)

furnitureLP:("max P = 3x1 + 2x2";"s.t";"2x1 + x2  <= 18";"2x1 + 3x2 <= 42";"3x1 + x2  <= 24";"xi >= 0 for all 1<=i<=2")

// Given LP, returns upper bound number of variables
nLPVars:{-3+(#x)+"J"$last("="\:last x)}

// Given an Fx, returns a 1 list, followed by a (possibly empy) list of
// 2-lists of (LinOp;Term). Casts the first element of each list as a float
// and the second as an int
linOpTermPairs:{{"FI"$'x}'"x"\:',/'|:|:'.q.cut[2;|:(" "\:x)]}

// Given a string Y representing an Fx, parses it into a list of coefficients
// for variables numbered by the value given as X
parseFx:{{@[x;-1+y 1;:;1f^(y 0)]}/[x#0f;linOpTermPairs y]}

parseObjective:{1f,(1-2*"max"~(" "\:y))*parseFx[x;" "/:3_(" "\:y)]}
