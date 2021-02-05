require open Stdlib.Bool Stdlib.Nat;

// Boolean equality on ℕ

symbol eq : ℕ → ℕ → 𝔹;

rule eq 0        0        ↪ true
with eq (suc $x) (suc $y) ↪ eq $x $y
with eq 0        (suc _ ) ↪ false
with eq (suc _ ) 0        ↪ false;

// Boolean less-than relation on ℕ

symbol le : ℕ → ℕ → 𝔹;

rule le 0        0        ↪ false
with le 0        (suc _ ) ↪ true
with le (suc $x) (suc $y) ↪ le $x $y;
