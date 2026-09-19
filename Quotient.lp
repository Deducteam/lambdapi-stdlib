/*
  Encoding of the Quotient types interfaces following the approch done in Lean.
*/
require open Stdlib.Eq;

symbol Rel a ≔ τ a → τ a → Prop;

[a:Set] (r:Rel a) inductive Quot : TYPE ≔ prj :τ a → Quot r;

constant symbol ⫽ : Π (a : Set), (τ a → τ a → Prop) → Set;
notation ⫽ infix 30;

rule τ (_ ⫽ $R) ↪ Quot $R;

symbol proj [a] r ≔ @prj a r;
symbol ind_quot [a] ≔ ind_Quot a;

symbol sound [a] (r:Rel a) x y: π(r x y) → π (proj r x = proj r y);

symbol lift [a] (r:Rel a) [b] (f:τ a → τ b):
  (Π x₁ x₁', π(r x₁ x₁') → π(f x₁ = f x₁')) → τ(a ⫽ r) → τ b;

rule lift _ $f _ (prj $x) ↪ $f $x;

symbol lift2 [a] (r:Rel a) (hr:Π x, π(r x x)) [b] (f:τ a → τ a → τ b)
  (hf:Π x₁ x₁', π(r x₁ x₁') → Π x₂ x₂', π(r x₂ x₂') → π(f x₁ x₂ = f x₁' x₂')):
  τ(a ⫽ r) → τ(a ⫽ r) → τ b ≔
begin
  assume a r hr b f hf;
  refine λ c d, lift r (λ x, lift r (f x) _ d) _ c
    { assume y y' yy'; apply hf {apply hr} {apply yy'} }
    { assume x x' xx'; set p ≔ λ x y y' yy', hf x x (hr x) y y' yy';
      change π(lift r (f x) (p x) d = lift r (f x') (p x') d);
      set q ≔ λ d, lift r (f x) (p x) d = lift r (f x') (p x') d;
      change π(q d); apply ind_quot r q _ d;
      assume y; simplify; apply hf {apply xx'} {apply hr} }
end;

assert (a:Set) (r:Rel a) (hr:Π x,π(r x x)) b (f:τ a → τ a → τ b)
  (hf:Π x₁ x₁', π(r x₁ x₁') → Π x₂ x₂', π(r x₂ x₂') → π(f x₁ x₂ = f x₁' x₂'))
  (x y:τ a) ⊢ lift2 r hr f hf (proj r x) (proj r y) ≡ f x y;

// Example from https://lawrencecpaulson.github.io/2022/03/30/Quotienting.html
// Let’s define the set of integers from pairs of natural numbers by quotienting.
// The required equivalence relation on such pairs is (a, b) ~ (c, d) ⟺ a + d = c + b
require open Stdlib.Nat Stdlib.Prod;

private symbol intrel : Rel (nat × nat) ≔ λ p q, (p ₁) + (q ₂) = (q ₁) + (p ₂);

private symbol int : Set ≔ (nat × nat) ⫽ intrel;

private symbol plus (p q : τ (nat × nat)) : τ (nat × nat) ≔ ((p ₁) + (q ₁)) ‚ ((p ₂) + (q ₂));

private opaque symbol plus_compat (p p' q q' : τ (nat × nat)) :
  π (intrel p p') → π (intrel q q') → π (intrel (plus p q) (plus p' q')) ≔
begin
  assume p p' q q' r s; simplify;
  rewrite addnACA (p ₁) (q ₁) (p' ₂) (q' ₂); rewrite r; rewrite s;
  rewrite addnACA (p' ₁) (q' ₁) (p ₂) (q ₂); reflexivity
end;

private symbol i+ : τ int → τ int → τ int ≔
  lift2 intrel (λ p, eq_refl _) (λ p q, proj intrel (plus p q))
    (λ p p' r q q' s, sound intrel (plus p q) (plus p' q') (plus_compat p p' q q' r s));

notation i+ infix left 20;

assert (p q : τ (nat × nat)) ⊢ proj intrel p i+ proj intrel q ≡ proj intrel (plus p q);

private opaque symbol i+_com (a b : τ int) : π (a i+ b = b i+ a) ≔
begin
  assume a b;
  refine ind_quot intrel (λ a, a i+ b = b i+ a) _ a; assume p;
  refine ind_quot intrel (λ b, proj intrel p i+ b = b i+ proj intrel p) _ b; assume q;
  refine feq (proj intrel) (feq2 (λ x y, x ‚ y) (addnC (p ₁) (q ₁)) (addnC (p ₂) (q ₂)))
end;