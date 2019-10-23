// Type of booleans

require open Set

symbol const bool : Set

definition B ≔ S bool

symbol const true : B
symbol const false : B

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
