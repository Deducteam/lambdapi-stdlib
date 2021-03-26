// (multi-sorted) First-order logic

require open Stdlib.Set Stdlib.Prop;

// Universal quantification

constant symbol ∀ {a} : (τ a → Prop) → Prop;

notation ∀ quantifier;

rule π (∀ $f) ↪ Π x, π ($f x);

// Existential quantification

constant symbol ∃ {a} : (τ a → Prop) → Prop;

notation ∃ quantifier;

constant symbol ex_intro {a} p (x:τ a) : π (p x) → π (∃ p);
symbol ex_elim {a} p q : π (∃ p) → (Π x:τ a, π (p x) → π q) → π q;
