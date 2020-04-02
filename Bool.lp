require open Stdlib.Set

// Type of booleans

constant symbol bool : Set

definition B ≔ τ bool

constant symbol true : B
constant symbol false : B

// Negation

symbol not : B ⇒ B

rule not true  → false
 and not false → true

// Disjunction

symbol or : B ⇒ B ⇒ B

set infix left 6 "|" ≔ or

rule true | _  → true
 and _  | true → true
 and false | &b → &b
 and &b | false → &b

// Conjunction

symbol {|and|} : B ⇒ B ⇒ B

set infix left 7 "^" ≔ {|and|}

rule true ^ &b → &b
 and &b ^ true → &b
 and false ^ _  → false
 and _  ^ false → false
