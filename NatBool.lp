require open Stdlib.Bool Stdlib.Nat

// Boolean equality on ℕ

symbol beq : ℕ → ℕ → B

rule beq 0        0        ↪ true
with beq (suc $x) (suc $y) ↪ beq $x $y
with beq 0        (suc _ ) ↪ false
with beq (suc _ ) 0        ↪ false

// Boolean less-than relation on ℕ

symbol ble : ℕ → ℕ → B

rule ble 0        0        ↪ false
with ble 0        (suc _ ) ↪ true
with ble (suc $x) (suc $y) ↪ ble $x $y
