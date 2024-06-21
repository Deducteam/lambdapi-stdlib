// (multi-sorted) First-order logic

require open Stdlib.Set Stdlib.Prop;

// Universal quantification

constant symbol ∀ [a] : (τ a → Prop) → Prop; // !! or \forall

notation ∀ quantifier;

rule π (∀ $f) ↪ Π x, π ($f x);

// Existential quantification

constant symbol ∃ [a] : (τ a → Prop) → Prop; // ?? or \exists

notation ∃ quantifier;

constant symbol ∃ᵢ [a p] (x:τ a) : π (p x) → π (∃ p);

symbol ∃ₑ [a p] : π (∃ p) → Π [q], (Π x:τ a, π (p x) → π q) → π q;

rule ∃ₑ (∃ᵢ $x $px) $f ↪ $f $x $px;

// properties

opaque symbol ¬∃ [a] p : π (¬ (∃ p) ⇒ `∀ x : τ a, ¬ (p x)) ≔
begin
assume a p not_ex_p x px; apply not_ex_p; apply ∃ᵢ x px
end;
