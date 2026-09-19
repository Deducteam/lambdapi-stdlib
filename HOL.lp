require open Stdlib.Set Stdlib.Eq;

constant symbol ⤳ : Set → Set → Set; // \leadsto

notation ⤳ infix right 20;

rule τ ($a ⤳ $b) ↪ τ $a → τ $b;

injective symbol ⤳d : Π a:Set, (τ a → Set) → Set;

notation ⤳d infix right 20;

rule $a ⤳d λ _,$b.[] ↪ $a ⤳ $b;

rule τ ($a ⤳d λ x,$b.[x]) ↪ Π x:τ $a, τ $b.[x];

symbol transport [a] (p: τ a → Set) [x y: τ a] : π (x = y) → τ (p x) → τ (p y);

rule @transport _ _ $x $x _ $u ↪ $u
with @transport _ (λ _, _) _ _ _ $u ↪ $u;