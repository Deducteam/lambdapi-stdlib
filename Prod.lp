// Cartesian product

require open Stdlib.Prop Stdlib.Set Stdlib.HOL Stdlib.Eq Stdlib.FOL;

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol ‚ [a b] : τ a → τ b → τ (a × b); notation ‚ infix right 30;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x ‚ y ‚ z : τ(a × b × c);
assert x y z ⊢ x ‚ y ‚ z ≡ x ‚ (y ‚ z);

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;

rule ($x ‚ _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;

rule (_ ‚ $x)₂ ↪ $x;

// Surjective pairing. `×` has no interpretation rule for `τ`, so it is opaque
// and η cannot be obtained by case analysis: we assume it.

symbol ×_η [a b] (x: τ (a × b)) : π ((x ₁) ‚ (x ₂) = x);

opaque symbol eq_₁ [a b] (x y: τ (a × b)) : π (x = y) → π ((x ₁) = (y ₁)) ≔
begin assume a b x y h; refine feq (λ z, z ₁) h end;

opaque symbol eq_₂ [a b] (x y: τ (a × b)) : π (x = y) → π ((x ₂) = (y ₂)) ≔
begin assume a b x y h; refine feq (λ z, z ₂) h end;

opaque symbol eq_pair [a b] (x y: τ (a × b)) :
  π ((x ₁) = (y ₁)) → π ((x ₂) = (y ₂)) → π (x = y) ≔
begin
  assume a b x y h1 h2;
  rewrite left (×_η x); rewrite left (×_η y);
  refine feq2 (λ u v, u ‚ v) h1 h2
end;

opaque symbol eq_×_iff [a b] (x y: τ (a × b)) :
  π (x = y ⇔ (x ₁) = (y ₁) ∧ (x ₂) = (y ₂)) ≔
begin
  assume a b x y; apply ∧ᵢ
    { assume h; apply ∧ᵢ { refine eq_₁ x y h } { refine eq_₂ x y h } }
    { assume h; refine eq_pair x y (∧ₑ₁ h) (∧ₑ₂ h) }
end;

opaque symbol ‚_inj₁ [a b] (x x': τ a) (y y': τ b) :
  π (x ‚ y = x' ‚ y') → π (x = x') ≔
begin assume a b x x' y y' h; refine eq_₁ (x ‚ y) (x' ‚ y') h end;

opaque symbol ‚_inj₂ [a b] (x x': τ a) (y y': τ b) :
  π (x ‚ y = x' ‚ y') → π (y = y') ≔
begin assume a b x x' y y' h; refine eq_₂ (x ‚ y) (x' ‚ y') h end;

symbol map_× [a b c d] (f: τ a → τ c) (g: τ b → τ d) (x: τ (a × b)) : τ (c × d) ≔
  f (x ₁) ‚ g (x ₂);

opaque symbol map_×_id [a b] (x: τ (a × b)) : π (map_× (λ u, u) (λ v, v) x = x) ≔
begin assume a b x; refine ×_η x end;

opaque symbol map_×_comp [a b c d e f]
  (g: τ c → τ e) (g': τ d → τ f) (h: τ a → τ c) (h': τ b → τ d) (x: τ (a × b)) :
  π (map_× g g' (map_× h h' x) = map_× (λ u, g (h u)) (λ v, g' (h' v)) x) ≔
begin assume a b c d e f g g' h h' x; reflexivity end;

// symmetry

symbol swap_× [a b] (x: τ (a × b)) : τ (b × a) ≔ (x ₂) ‚ (x ₁);

opaque symbol swap_×_invol [a b] (x: τ (a × b)) : π (swap_× (swap_× x) = x) ≔
begin assume a b x; refine ×_η x end;

// universal property: a map into a product is a pair of maps

symbol pairing [a b c] (f: τ (c ⤳ a)) (g: τ (c ⤳ b)) : τ (c ⤳ (a × b)) ≔
  λ z, f z ‚ g z;

opaque symbol ₁_pairing [a b c] (f: τ (c ⤳ a)) (g: τ (c ⤳ b)) (z: τ c) :
  π ((pairing f g z ₁) = f z) ≔
begin assume a b c f g z; reflexivity end;

opaque symbol ₂_pairing [a b c] (f: τ (c ⤳ a)) (g: τ (c ⤳ b)) (z: τ c) :
  π ((pairing f g z ₂) = g z) ≔
begin assume a b c f g z; reflexivity end;

opaque symbol pairing_uniq [a b c] (h: τ (c ⤳ (a × b))) (z: τ c) :
  π (pairing (λ u, h u ₁) (λ u, h u ₂) z = h z) ≔
begin assume a b c h z; refine ×_η (h z) end;



// Co-Cartesian product

(a: Set) (b: Set) inductive Sum: TYPE ≔
| inl: τ a → Sum a b
| inr: τ b → Sum a b
;

constant symbol sum : Set → Set → Set;

rule τ (sum $a $b) ↪ Sum $a $b;

// Universal property: a map out of a sum is given by case analysis

symbol sum_case [a b c] : τ (sum a b) → (τ a → τ c) → (τ b → τ c) → τ c;

rule sum_case (inl $x) $f _ ↪ $f $x
with sum_case (inr $y) _ $g ↪ $g $y;

opaque symbol sum_case_uniq [a b c] (h: τ (sum a b) → τ c) (s: τ (sum a b)) :
  π (sum_case s (λ x, h (inl x)) (λ y, h (inr y)) = h s) ≔
begin
  assume a b c h; induction { assume x; reflexivity } { assume y; reflexivity }
end;

opaque symbol sum_η [a b] (s: τ (sum a b)) :
  π (sum_case s (λ x, inl x) (λ y, inr y) = s) ≔
begin
  assume a b; induction { assume x; reflexivity } { assume y; reflexivity }
end;

// non confusion of constructors
symbol is_inl [a b] : τ (sum a b) → Prop;

rule is_inl (inl _) ↪ ⊤
with is_inl (inr _) ↪ ⊥;

opaque symbol inr≠inl [a b] (x: τ a) (y: τ b) : π (@inr a b y ≠ inl x) ≔
begin assume a b x y h; refine ind_eq h (λ s, is_inl s) ⊤ᵢ end;

opaque symbol inl≠inr [a b] (x: τ a) (y: τ b) : π (@inl a b x ≠ inr y) ≔
begin assume a b x y h; apply inr≠inl x y; symmetry; apply h end;

symbol outl [a b] (s: τ (sum a b)) : τ a ≔ sum_case s (λ x, x) (λ _, el a);
symbol outr [a b] (s: τ (sum a b)) : τ b ≔ sum_case s (λ _, el b) (λ y, y);

opaque symbol inl_inj [a b] (x x': τ a) : π (@inl a b x = inl x') → π (x = x') ≔
begin assume a b x x' h; refine feq (λ s, @outl a b s) h end;

opaque symbol inr_inj [a b] (y y': τ b) : π (@inr a b y = inr y') → π (y = y') ≔
begin assume a b y y' h; refine feq (λ s, @outr a b s) h end;

// induction principle with equalities

opaque symbol case_Sum [a b] (s: τ (sum a b)) :
  π ((`∃ x, s = inl x) ∨ (`∃ y, s = inr y)) ≔
begin
  assume a b; induction
  { assume x; apply ∨ᵢ₁; apply ∃ᵢ x; reflexivity }
  { assume y; apply ∨ᵢ₂; apply ∃ᵢ y; reflexivity }
end;

opaque symbol ind_Sum_eq [a b] (p: τ (sum a b) → Prop) (s: τ (sum a b)) :
  (Π x, π (s = inl x) → π (p s)) → (Π y, π (s = inr y) → π (p s)) → π (p s) ≔
begin
  assume a b p s hl hr; refine ∨ₑ (case_Sum s) (λ h, ∃ₑ h hl) (λ h, ∃ₑ h hr)
end;

symbol map_sum [a b c d] (f: τ a → τ c) (g: τ b → τ d) (s: τ (sum a b))
  : τ (sum c d) ≔ sum_case s (λ x, inl (f x)) (λ y, inr (g y));

opaque symbol map_sum_id [a b] (s: τ (sum a b)) :
  π (map_sum (λ u, u) (λ v, v) s = s) ≔
begin assume a b s; refine sum_η s end;

opaque symbol map_sum_comp [a b c d e f]
  (g: τ c → τ e) (g': τ d → τ f) (h: τ a → τ c) (h': τ b → τ d) (s: τ (sum a b)) :
  π (map_sum g g' (map_sum h h' s) = map_sum (λ u, g (h u)) (λ v, g' (h' v)) s) ≔
begin
  assume a b c d e f g g' h h';
  induction { assume x; reflexivity } { assume y; reflexivity }
end;

symbol swap_sum [a b] (s: τ (sum a b)) : τ (sum b a) ≔
  sum_case s (λ x, inr x) (λ y, inl y);

opaque symbol swap_sum_invol [a b] (s: τ (sum a b)) :
  π (swap_sum (swap_sum s) = s) ≔
begin
  assume a b; induction { assume x; reflexivity } { assume y; reflexivity }
end;

// Relation between the product and the coproduct
symbol dist_× [a b c] (x: τ (a × sum b c)) : τ (sum (a × b) (a × c)) ≔
  sum_case (x ₂) (λ y, inl ((x ₁) ‚ y)) (λ z, inr ((x ₁) ‚ z));

symbol undist_× [a b c] (s: τ (sum (a × b) (a × c))) : τ (a × sum b c) ≔
  sum_case s (λ u, (u ₁) ‚ inl (u ₂)) (λ v, (v ₁) ‚ inr (v ₂));

opaque symbol undist_dist_‚ [a b c] (u: τ a) (s: τ (sum b c)) :
  π (undist_× (dist_× (u ‚ s)) = u ‚ s) ≔
begin
  assume a b c u; induction { assume y; reflexivity } { assume z; reflexivity }
end;

opaque symbol undist_dist_× [a b c] (x: τ (a × sum b c)) :
  π (undist_× (dist_× x) = x) ≔
begin
  assume a b c x; rewrite left (×_η x); refine undist_dist_‚ (x ₁) (x ₂)
end;

opaque symbol dist_undist_× [a b c] (s: τ (sum (a × b) (a × c))) :
  π (dist_× (undist_× s) = s) ≔
begin
  assume a b c; induction
  { assume u; refine feq (λ w, @inl (a × b) (a × c) w) (×_η u) }
  { assume v; refine feq (λ w, @inr (a × b) (a × c) w) (×_η v) }
end;

symbol sum_curry [a b c] (h: τ (sum a b ⤳ c)) : τ ((a ⤳ c) × (b ⤳ c)) ≔
  (λ x, h (inl x)) ‚ (λ y, h (inr y));

symbol sum_uncurry [a b c] (fg: τ ((a ⤳ c) × (b ⤳ c))) : τ (sum a b ⤳ c) ≔
  λ s, sum_case s (fg ₁) (fg ₂);

opaque symbol sum_uncurry_curry [a b c] (h: τ (sum a b ⤳ c)) (s: τ (sum a b)) :
  π (sum_uncurry (sum_curry h) s = h s) ≔
begin
  assume a b c h; induction { assume x; reflexivity } { assume y; reflexivity }
end;

opaque symbol sum_curry_uncurry₁ [a b c] (fg: τ ((a ⤳ c) × (b ⤳ c))) (x: τ a) :
  π (((sum_curry (sum_uncurry fg)) ₁) x = (fg ₁) x) ≔
begin assume a b c fg x; reflexivity end;

opaque symbol sum_curry_uncurry₂ [a b c] (fg: τ ((a ⤳ c) × (b ⤳ c))) (y: τ b) :
  π (((sum_curry (sum_uncurry fg)) ₂) y = (fg ₂) y) ≔
begin assume a b c fg y; reflexivity end;





// Dependent pair of an element and a proof

[a: Set] (p: τ a → Prop) inductive Σ : TYPE ≔
  exist (x: τ a) : π (p x) → Σ p;

symbol s₁ [a] [p] (e: @Σ a p) : τ a;
notation s₁ postfix 12;

rule (exist $x _) s₁ ↪ $x;

symbol s₂ [a] [p] (e: @Σ a p) : π (p (e s₁));
notation s₂ postfix 12;

rule (exist _ $h) s₂ ↪ $h;

opaque symbol Σ_∃ [a] [p] (e: @Σ a p) : π (`∃ x, p x) ≔
begin assume a p e; refine ∃ᵢ (e s₁) (e s₂) end;

constant symbol Sigma [a] (p: τ a → Prop) : π (`∃ x, p x) → Set;

rule τ (@Sigma $a $p _) ↪ @Σ $a $p;

opaque symbol Σ_η [a] [p] [h] (e: τ (@Sigma a p h)) : π (exist (e s₁) (e s₂) = e) ≔
begin assume a p h; induction; assume x hx; reflexivity end;

opaque symbol eq_s₁ [a] [p] [h] (x y: τ (@Sigma a p h)) : π (x = y) → π (x s₁ = y s₁) ≔
begin assume a p h x y e; refine feq (λ z, z s₁) e end;

opaque symbol exist_inj [a] [p] [h] (x y: τ a) (hx: π (p x)) (hy: π (p y)) :
  π (@= (@Sigma a p h) (exist x hx) (exist y hy)) → π (x = y) ≔
begin assume a p h x y hx hy e; refine @eq_s₁ a p h (exist x hx) (exist y hy) e end;


// Dependent pair of an element and an element in Set

[a: Set] (p: τ a → Set) inductive sigT : TYPE ≔
  exisT (x: τ a) : τ (p x) → sigT p;

constant symbol SigmaT [a: Set] : (τ a → Set) → Set;

rule τ (@SigmaT $a $p) ↪ @sigT $a $p;


symbol st₁ [a] [p] (e: @sigT a p) : τ a;
notation st₁ postfix 12;

rule (exisT $x _) st₁ ↪ $x;

symbol st₂ [a] [p] (e: @sigT a p) : τ (p (e st₁));
notation st₂ postfix 12;

rule (exisT _ $u) st₂ ↪ $u;

opaque symbol sigT_η [a] [p] (e: @sigT a p) : π (exisT (e st₁) (e st₂) = e) ≔
begin assume a p; induction; assume x u; reflexivity end;

opaque symbol eq_st₁ [a] [p] (x y: @sigT a p) : π (x = y) → π (x st₁ = y st₁) ≔
begin assume a p x y h; refine feq (λ e, e st₁) h end;

symbol eq_exisT [a] [p] (x y: τ a) (u: τ (p x)) (v: τ (p y)) (h: π (x = y)) :
  π (transport p h u = v) → π (@exisT a p x u = exisT y v);

opaque symbol eq_exisT_refl [a] [p] (x: τ a) (u v: τ (p x)) :
  π (u = v) → π (@exisT a p x u = exisT x v) ≔
begin
  assume a p x u v h; refine feq (λ w, @exisT a p x w) h
end;
