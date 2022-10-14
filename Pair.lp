// Cartesian product

require open Blanqui.Lib.Set;

injective symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol & [a b] : τ a → τ b → τ (a × b); notation & infix right 30;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x & y & z : τ(a × b × c);
assert x y z ⊢ x & y & z ≡ x & (y & z);
