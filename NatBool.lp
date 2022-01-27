require open Blanqui.Lib.Bool Blanqui.Lib.Nat;

// Boolean equality on ℕ

symbol = : ℕ → ℕ → 𝔹;

notation = infix 10;

rule 0 = 0 ↪ true
with s $x = s $y ↪ $x = $y
with 0 = s _ ↪ false
with s _ = 0 ↪ false;

// Boolean less-than relation on ℕ

symbol ≤ : ℕ → ℕ → 𝔹;

notation ≤ infix 10;

rule 0 ≤ 0 ↪ false
with 0 ≤ s _ ↪ true
with s $x ≤ s $y ↪ $x ≤ $y;
