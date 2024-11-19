require open Stdlib.Set;

symbol ⤳ : Set → Set → Set; notation ⤳ infix right 10;

rule τ ($x ⤳ $y) ↪ τ $x → τ $y;
