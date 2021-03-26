// Booleans

require open Stdlib.Set Stdlib.Prop Stdlib.FOL;

inductive 𝔹 : TYPE ≔
| true : 𝔹
| false : 𝔹;

// set code for 𝔹

constant symbol bool : Set;

rule τ bool ↪ 𝔹;

// 𝔹oolean not

symbol not : 𝔹 → 𝔹;

rule not true  ↪ false
with not false ↪ true;

// 𝔹oolean or

symbol or : 𝔹 → 𝔹 → 𝔹;

notation or infix left 6;

rule true  or _     ↪ true
with _     or true  ↪ true
with false or $b    ↪ $b
with $b    or false ↪ $b;

// 𝔹oolean and

symbol and : 𝔹 → 𝔹 → 𝔹;

notation and infix left 7;

rule true  and $b    ↪ $b
with $b    and true  ↪ $b
with false and _     ↪ false
with _     and false ↪ false;

// Conditional

symbol if : 𝔹 → Π {a}, τ a → τ a → τ a;

rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;
