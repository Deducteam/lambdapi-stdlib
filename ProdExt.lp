// Extensionality of the Cartesian product

require open Stdlib.FOL Stdlib.Eq Stdlib.Prod;

/* Surjective pairing. `×` has no interpretation rule for `τ`, so it is opaque
   and η cannot be obtained by case analysis: we assume it. */

symbol prodExt [a b] (x: τ (a × b)) : π (x = (x ₁) ‚ (x ₂));

opaque symbol eq_pair [a b] (x y: τ (a × b)) :
  π ((x ₁) = (y ₁)) → π ((x ₂) = (y ₂)) → π (x = y) ≔
begin
  assume a b x y h1 h2;
  rewrite (prodExt x); rewrite (prodExt y);
  refine feq2 (λ u v, u ‚ v) h1 h2
end;

opaque symbol eq_×_iff [a b] (x y: τ (a × b)) :
  π (x = y ⇔ (x ₁) = (y ₁) ∧ (x ₂) = (y ₂)) ≔
begin
  assume a b x y; apply ∧ᵢ
    { assume h; apply ∧ᵢ { refine eq_₁ x y h } { refine eq_₂ x y h } }
    { assume h; refine eq_pair x y (∧ₑ₁ h) (∧ₑ₂ h) }
end;

opaque symbol map_×_id [a b] (x: τ (a × b)) : π (map_× (λ u, u) (λ v, v) x = x) ≔
begin assume a b x; symmetry; refine prodExt x end;

opaque symbol swap_×_invol [a b] (x: τ (a × b)) : π (swap_× (swap_× x) = x) ≔
begin assume a b x; symmetry; refine prodExt x end;

opaque symbol pairing_uniq [a b c] (h: τ c → τ (a × b)) (z: τ c) :
  π (pairing (λ u, h u ₁) (λ u, h u ₂) z = h z) ≔
begin assume a b c h z; symmetry; refine prodExt (h z) end;
