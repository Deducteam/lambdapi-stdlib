require open Bool Nat

// Boolean equality

symbol beq : N ⇒ N ⇒ B

rule beq 0         0         → tt
 and beq (succ &x) (succ &y) → beq &x &y
 and beq 0         (succ _ ) → ff
 and beq (succ _ ) 0         → ff

// Boolean less-than

symbol ble : N ⇒ N ⇒ B

rule ble 0         0         → ff
 and ble 0         (succ _ ) → tt
 and ble (succ &x) (succ &y) → ble &x &y
