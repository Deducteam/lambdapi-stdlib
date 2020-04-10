require open Stdlib.Bool Stdlib.Nat

// Boolean equality on ℕ

symbol beq : ℕ ⇒ ℕ ⇒ B

rule beq 0         0         → true
 and beq (succ &x) (succ &y) → beq &x &y
 and beq 0         (succ _ ) → false
 and beq (succ _ ) 0         → false

// Boolean less-than relation on ℕ

symbol ble : ℕ ⇒ ℕ ⇒ B

rule ble 0         0         → false
 and ble 0         (succ _ ) → true
 and ble (succ &x) (succ &y) → ble &x &y
