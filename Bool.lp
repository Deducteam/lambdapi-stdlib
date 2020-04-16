require open Stdlib.Set

// Type of booleans

constant symbol bool : Set

definition B ≔ τ bool

constant symbol true : B
constant symbol false : B

// Negation

symbol not : B → B

rule not true  ↪ false
 with not false ↪ true

// Disjunction

symbol or : B → B → B

set infix left 6 "|" ≔ or

rule true | _  ↪ true
 with _  | true ↪ true
 with false | $b ↪ $b
 with $b | false ↪ $b

// Conjunction

symbol {|and|} : B → B → B

set infix left 7 "^" ≔ {|and|}

rule true ^ $b ↪ $b
 with $b ^ true ↪ $b
 with false ^ _  ↪ false
 with _  ^ false ↪ false
