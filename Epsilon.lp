require open Stdlib.FOL Stdlib.FunExt Stdlib.Impred;

symbol ε [a:Set] : (τ a → Prop) → τ a;
symbol εᵢ [a:Set] (p:τ a → Prop) : π (∃ p) → π (p (ε p));

opaque symbol εₑ [a:Set] (p:τ a → Prop) : π (p (ε p)) → π (∃ p) ≔
begin
  assume a p h;
  have e : π ((λ x, p x) = p) { refine funExt (λ x, p x) p (λ x, eq_refl (p x)) };
  rewrite left e;
  refine ∃ᵢ (ε p) h
end;