require open Stdlib.Bool Stdlib.Nat

// Boolean equality on ℕ

symbol beq : ℕ → ℕ → B

rule beq 0         0         ⟶ true
 with beq (succ $x) (succ $y) ⟶ beq $x $y
 with beq 0         (succ _ ) ⟶ false
 with beq (succ _ ) 0         ⟶ false

// Boolean less-than relation on ℕ

symbol ble : ℕ → ℕ → B

rule ble 0         0         ⟶ false
 with ble 0         (succ _ ) ⟶ true
 with ble (succ $x) (succ $y) ⟶ ble $x $y
