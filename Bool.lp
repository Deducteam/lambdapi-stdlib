/* Library on booleans. */

require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.FOL Blanqui.Lib.Eq;

inductive 𝔹 : TYPE ≔ // `dB or \BbbB
| true : 𝔹
| false : 𝔹;

constant symbol bool : Set;

rule τ bool ↪ 𝔹;

// induction principle with equalities

opaque symbol case_𝔹 b : π (b = true ∨ b = false) ≔
begin
  induction
  { apply ∨ᵢ₁; reflexivity; }
  { apply ∨ᵢ₂; reflexivity; }
end;

opaque symbol ind_𝔹_eq p b:
 (π(b = true) → π(p b)) → (π(b = false) → π(p b)) → π(p b) ≔
begin
  assume p b t f; refine ∨ₑ (case_𝔹 b) t f;
end;

// non confusion of constructors

symbol istrue : 𝔹 → Prop;

rule istrue true ↪ ⊤
with istrue false ↪ ⊥;

opaque symbol false≠true : π (false ≠ true) ≔
begin
  assume h; refine ind_eq h istrue top
end;

opaque symbol true≠false : π (true ≠ false) ≔
begin
  assume h; apply false≠true; symmetry; apply h
end;

// not

symbol not : 𝔹 → 𝔹;

rule not true  ↪ false
with not false ↪ true;

// or

symbol or : 𝔹 → 𝔹 → 𝔹; notation or infix left 20;

rule true  or _     ↪ true
with _     or true  ↪ true
with false or $b    ↪ $b
with $b    or false ↪ $b;

opaque symbol ∨_istrue [p q] : π(istrue(p or q)) → π(istrue p ∨ istrue q) ≔
begin
  induction
  { assume q h; apply ∨ᵢ₁; apply top; }
  { assume q h; apply ∨ᵢ₂; apply h; }
end;

opaque symbol istrue_or [p q] : π(istrue p ∨ istrue q) → π(istrue(p or q)) ≔
begin
  induction
  { assume q h; apply top; }
  { assume q h; apply ∨ₑ h { assume i; apply ⊥ₑ i; } { assume i; apply i; } }
end;

opaque symbol orᵢ₁ [p] q : π (istrue p) → π (istrue (p or q)) ≔
begin
  induction
  { simplify; assume b h; apply top }
  { simplify; assume b h; apply ⊥ₑ h }
end;

opaque symbol orᵢ₂ p [q] : π (istrue q) → π (istrue (p or q)) ≔
begin
  induction
  { simplify; assume b h; apply top }
  { simplify; assume b h; apply h }
end;

opaque symbol orₑ [p q] r : π(istrue(p or q)) →
  (π(istrue p) → π(istrue r)) → (π(istrue q) → π(istrue r)) → π(istrue r) ≔
begin
  assume p q r pq pr qr;
  have h: π(istrue p ∨ istrue q) { apply @∨_istrue p q pq /*FIXME*/ };
  apply ∨ₑ h pr qr;
end;

opaque symbol orC p q : π (p or q = q or p) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

opaque symbol orA p q r : π ((p or q) or r = p or (q or r)) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

// and

symbol and : 𝔹 → 𝔹 → 𝔹; notation and infix left 7;

rule true  and $b    ↪ $b
with $b    and true  ↪ $b
with false and _     ↪ false
with _     and false ↪ false;

opaque symbol ∧_istrue [p q] : π(istrue (p and q)) → π(istrue p ∧ istrue q) ≔
begin
  induction
  { induction
    { assume h; apply ∧ᵢ { apply top } { apply top } }
    { assume h; apply ⊥ₑ h; }
  }
  { assume q h; apply ⊥ₑ h; }
end;

opaque symbol istrue_and [p q] : π(istrue p ∧ istrue q) → π(istrue (p and q)) ≔
begin
  induction
  { assume q h; apply ∧ₑ₂ h; }
  { assume q h; apply ∧ₑ₁ h; }
end;

opaque symbol andᵢ [p q] : π(istrue p) → π(istrue q) → π(istrue (p and q)) ≔
begin
  assume p q h i; //FIXME: apply istrue_and fails
  apply @istrue_and p q; apply ∧ᵢ h i;
end;

opaque symbol andₑ₁ [p q] : π (istrue (p and q)) → π (istrue p) ≔
begin
  induction
  { assume q i; apply top; }
  { assume q i; apply i; }
end;

opaque symbol andₑ₂ [p q] : π (istrue (p and q)) → π (istrue q) ≔
begin
  induction
  { assume q i; apply i; }
  { assume q i; apply ⊥ₑ i; }
end;

// if-then-else

symbol if : 𝔹 → Π [a], τ a → τ a → τ a;

rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;

