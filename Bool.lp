require open Stdlib.Set Stdlib.Logic;

// Type of booleans

inductive 𝔹 : TYPE ≔
| true : 𝔹
| false : 𝔹;

symbol bool : Set;

rule 𝔹 ↪ τ bool;

// 𝔹oolean not

symbol not : 𝔹 → 𝔹;

rule not true  ↪ false
with not false ↪ true;

// 𝔹oolean or

symbol or : 𝔹 → 𝔹 → 𝔹;

set infix left 6 "||" ≔ or;

rule true  || _     ↪ true
with _     || true  ↪ true
with false || $b    ↪ $b
with $b    || false ↪ $b;

// 𝔹oolean and

symbol and : 𝔹 → 𝔹 → 𝔹;

set infix left 7 "^" ≔ and;

rule true  ^ $b    ↪ $b
with $b    ^ true  ↪ $b
with false ^ _     ↪ false
with _     ^ false ↪ false;

// Conditional

symbol if : 𝔹 → Π{a}, τ a → τ a → τ a;

rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;
