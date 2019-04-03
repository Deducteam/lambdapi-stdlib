// Type of booleans

symbol const B : TYPE

symbol const tt : B
symbol const ff : B

// Negation

symbol bnot : B ⇒ B

rule bnot tt → ff
 and bnot ff → tt

// Disjunction

symbol bor : B ⇒ B ⇒ B

set infix left 6 "|" ≔ bor

rule tt | _  → tt
 and _  | tt → tt
 and ff | &b → &b
 and &b | ff → &b

// Conjunction

symbol band : B ⇒ B ⇒ B

set infix left 7 "&" ≔ band

rule tt & &b → &b
 and &b & tt → &b
 and ff & _  → ff
 and _  & ff → ff
