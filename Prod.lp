// Cartesian product

require open Stdlib.Prop Stdlib.Set Stdlib.Eq;

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol ‚ [a b] : τ a → τ b → τ (a × b); notation ‚ infix right 30;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x ‚ y ‚ z : τ(a × b × c);
assert x y z ⊢ x ‚ y ‚ z ≡ x ‚ (y ‚ z);

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;

rule ($x ‚ _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;

rule (_ ‚ $x)₂ ↪ $x;

opaque symbol eq_₁ [a b] (x y: τ (a × b)) : π (x = y) → π ((x ₁) = (y ₁)) ≔
begin assume a b x y h; refine feq (λ z, z ₁) h end;

opaque symbol eq_₂ [a b] (x y: τ (a × b)) : π (x = y) → π ((x ₂) = (y ₂)) ≔
begin assume a b x y h; refine feq (λ z, z ₂) h end;

opaque symbol ‚_inj₁ [a b] (x x': τ a) (y y': τ b) :
  π (x ‚ y = x' ‚ y') → π (x = x') ≔
begin assume a b x x' y y' h; refine eq_₁ (x ‚ y) (x' ‚ y') h end;

opaque symbol ‚_inj₂ [a b] (x x': τ a) (y y': τ b) :
  π (x ‚ y = x' ‚ y') → π (y = y') ≔
begin assume a b x x' y y' h; refine eq_₂ (x ‚ y) (x' ‚ y') h end;

symbol map_× [a b c d] (f: τ a → τ c) (g: τ b → τ d) (x: τ (a × b)) : τ (c × d) ≔
  f (x ₁) ‚ g (x ₂);

opaque symbol map_×_comp [a b c d e f]
  (g: τ c → τ e) (g': τ d → τ f) (h: τ a → τ c) (h': τ b → τ d) (x: τ (a × b)) :
  π (map_× g g' (map_× h h' x) = map_× (λ u, g (h u)) (λ v, g' (h' v)) x) ≔
begin reflexivity end;

symbol swap_× [a b] (x: τ (a × b)) : τ (b × a) ≔ (x ₂) ‚ (x ₁);

symbol pairing [a b c] (f: τ c → τ a) (g: τ c → τ b) : τ c → τ (a × b) ≔
  λ z, f z ‚ g z;

opaque symbol ₁_pairing [a b c] (f: τ c → τ a) (g: τ c → τ b) (z: τ c) :
  π ((pairing f g z ₁) = f z) ≔
begin reflexivity end;

opaque symbol ₂_pairing [a b c] (f: τ c → τ a) (g: τ c → τ b) (z: τ c) :
  π ((pairing f g z ₂) = g z) ≔
begin reflexivity end;
