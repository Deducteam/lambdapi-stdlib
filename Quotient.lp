// Quotient types

require open Stdlib.Eq;

symbol Rel a ≔ τ a → τ a → Prop;

[a:Set] (r:Rel a) inductive Quot : TYPE ≔ prj:τ a → Quot r;

constant symbol ⫽ : Π a, (τ a → τ a → Prop) → Set; // \sslash
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
