// This module turns proved equalities to rewrite rules

require open Stdlib.Bool;
require Stdlib.Nat as N;
require open Stdlib.List;
require Stdlib.Pos as P;
require Stdlib.Z as Z;

// Bool

rule _ or true  ↪ true
with $b or false ↪ $b;

// Nat

rule $x N.+ N._0 ↪ $x;
rule $x N.+ $y N.+1 ↪ ($x N.+ $y) N.+1;
rule ($x N.+ $y) N.+ $z ↪ $x N.+ ($y N.+ $z);
rule $x N.- N._0 ↪ $x;
rule _ N.* N._0 ↪ N._0;
rule N.max $x N._0 ↪ $x;
rule N.max $x $x ↪ $x;
rule N.min _ N._0 ↪ N._0;
rule N.min $x $x ↪ $x;

// List

rule $m ++ □ ↪ $m;
rule size ($l ++ $m) ↪ size $l N.+ size $m;
rule ($l ++ $m) ++ $n ↪ $l ++ ($m ++ $n);
rule last _ ($e ⸬ $l) ↪ last $e $l;
rule nth $x □ _ ↪ $x;
rule drop _ □ ↪ □;
rule take _ □ ↪ □;

// Pos

rule P.add $x P.H ↪ P.succ $x
with P.add P.H $y ↪ P.succ $y;
rule P.add_carry $x P.H ↪ P.add $x (P.O P.H)
with P.add_carry P.H $y ↪ P.add (P.O P.H) $y;
rule P.mul $x P.H ↪ $x;

// Z

rule $x Z.+ Z.Z0 ↪ $x;
