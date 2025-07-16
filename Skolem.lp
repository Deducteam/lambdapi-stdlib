require open Stdlib.Prop Stdlib.FOL Stdlib.Epsilon;

// procedure for skolemizing all existentials
// /!\ WARNING: this is a sequential symbol

private sequential symbol skolem: Prop → Prop;
private sequential symbol skolem-: Prop → Prop;

rule skolem (∀ $p) ↪ `∀ x, skolem ($p x)
with skolem (∃ $p) ↪ skolem ($p (ε $p))
with skolem ($p ∧ $q) ↪ skolem $p ∧ skolem $q
with skolem ($p ∨ $q) ↪ skolem $p ∨ skolem $q
with skolem ($p ⇒ $q) ↪ skolem- $p ⇒ skolem $q
with skolem $p ↪ $p

with skolem- (∀ $p) ↪ skolem- ($p (ε $p))
with skolem- (∃ $p) ↪ `∃ x, skolem- ($p x)
with skolem- ($p ∧ $q) ↪ skolem- $p ∧ skolem- $q
with skolem- ($p ∨ $q) ↪ skolem- $p ∨ skolem- $q
with skolem- ($p ⇒ $q) ↪ skolem $p ⇒ skolem- $q
with skolem- $p ↪ $p;

// example

require open Stdlib.Set Stdlib.Nat;

private symbol P:ℕ → TYPE;

rule P 0 ↪ Prop
with P ($n +1) ↪ τ ι → P $n;

private symbol p : P 2;
private symbol q : P 4;

private symbol A ≔ `∀ X1, `∃ X2, p X1 X2 ∧ `∀ X3, `∃ X4, q X1 X2 X3 X4;

private symbol sk1 X1 ≔ ε (λ X2, p X1 X2 ∧ `∀ X3, `∃ X4, q X1 X2 X3 X4);

private symbol B ≔ `∀ X1, p X1 (sk1 X1) ∧ `∀ X3, `∃ X4, q X1 (sk1 X1) X3 X4;

private symbol sk2 X1 X3 ≔ ε (λ X4, q X1 (sk1 X1) X3 X4);

private symbol C ≔ `∀ X1, p X1 (sk1 X1) ∧ `∀ X3, q X1 (sk1 X1) X3 (sk2 X1 X3);

assert ⊢ skolem A ≡ C;

// propositional atoms

symbol at:ℕ → Prop;

// we assume that Prop is inductive

symbol ind_Prop (p:Prop → Prop):
(Π k, π(p (at k))) →
(Π a f, π((`∀ x:τ a, p (f x)) ⇒ p (∃ f))) →
(Π a f, π((`∀ x:τ a, p (f x)) ⇒ p (∀ f))) →
(Π f g, π(p f ⇒ p g ⇒ p (f ∧ g))) →
(Π f g, π(p f ⇒ p g ⇒ p (f ∨ g))) →
(Π f g, π(p f ⇒ p g ⇒ p (f ⇒ g))) →
Π f:Prop, π(p f);

// positions in a proposition

inductive Pos : TYPE ≔
| top: Pos
| all: Pos → Pos
| ex: Pos → Pos
| and1: Pos → Pos
| and2: Pos → Pos
| or1: Pos → Pos
| or2: Pos → Pos
| imp1: Pos → Pos
| imp2: Pos → Pos;

// valid positions

symbol valid: Pos → Prop → Prop;

rule valid top (at _) ↪ ⊥
with valid top (∃ _) ↪ ⊤
with valid top (∀ _) ↪ ⊥
with valid top (_ ∧ _) ↪ ⊥
with valid top (_ ∨ _) ↪ ⊥
with valid top (_ ⇒ _) ↪ ⊥

with valid (all _) (at _) ↪ ⊥
with valid (all _) (∃ _) ↪ ⊥
with valid (all $i) (∀ $f) ↪ `∀ x, valid $i ($f x)
with valid (all _) (_ ∧ _) ↪ ⊥
with valid (all _) (_ ∨ _) ↪ ⊥
with valid (all _) (_ ⇒ _) ↪ ⊥

with valid (ex _) (at _) ↪ ⊥
with valid (ex $i) (∃ $f) ↪ `∀ x, valid $i ($f x)
with valid (ex _) (∀ _) ↪ ⊥
with valid (ex _) (_ ∧ _) ↪ ⊥
with valid (ex _) (_ ∨ _) ↪ ⊥
with valid (ex _) (_ ⇒ _) ↪ ⊥

with valid (and1 _) (at _) ↪ ⊥
with valid (and1 _) (∃ _) ↪ ⊥
with valid (and1 _) (∀ _) ↪ ⊥
with valid (and1 $i) ($f ∧ _) ↪ valid $i $f
with valid (and1 _) (_ ∨ _) ↪ ⊥
with valid (and1 _) (_ ⇒ _) ↪ ⊥

with valid (and2 _) (at _) ↪ ⊥
with valid (and2 _) (∃ _) ↪ ⊥
with valid (and2 _) (∀ _) ↪ ⊥
with valid (and2 $i) (_ ∧ $f) ↪ valid $i $f
with valid (and2 _) (_ ∨ _) ↪ ⊥
with valid (and2 _) (_ ⇒ _) ↪ ⊥

with valid (or1 _) (at _) ↪ ⊥
with valid (or1 _) (∃ _) ↪ ⊥
with valid (or1 _) (∀ _) ↪ ⊥
with valid (or1 _) (_ ∧ _) ↪ ⊥
with valid (or1 $i) ($f ∨ _) ↪ valid $i $f
with valid (or1 _) (_ ⇒ _) ↪ ⊥

with valid (or2 _) (at _) ↪ ⊥
with valid (or2 _) (∃ _) ↪ ⊥
with valid (or2 _) (∀ _) ↪ ⊥
with valid (or2 _) (_ ∧ _) ↪ ⊥
with valid (or2 $i) (_ ∨ $f) ↪ valid $i $f
with valid (or2 _) (_ ⇒ _) ↪ ⊥

with valid (imp1 _) (at _) ↪ ⊥
with valid (imp1 _) (∃ _) ↪ ⊥
with valid (imp1 _) (∀ _) ↪ ⊥
with valid (imp1 _) (_ ∧ _) ↪ ⊥
with valid (imp1 _) (_ ∨ _) ↪ ⊥
with valid (imp1 $i) ($f ⇒ _) ↪ valid $i $f

with valid (imp2 _) (at _) ↪ ⊥
with valid (imp2 _) (∃ _) ↪ ⊥
with valid (imp2 _) (∀ _) ↪ ⊥
with valid (imp2 _) (_ ∧ _) ↪ ⊥
with valid (imp2 _) (_ ∨ _) ↪ ⊥
with valid (imp2 $i) (_ ⇒ $f) ↪ valid $i $f
;

// induction principle on valid positions

require open Stdlib.Impred;

opaque symbol ind_valid (p:Pos → Prop → Prop):
(Π a (f:τ a → Prop), π(p top (∃ f))) →
(Π i a (f:τ a → Prop),
  π((`∀ x, valid i (f x)) ⇒ (`∀ x, p i (f x)) ⇒ p (all i) (∀ f))) →
(Π i a (f:τ a → Prop),
  π((`∀ x, valid i (f x)) ⇒ (`∀ x, p i (f x)) ⇒ p (ex i) (∃ f))) →
(Π i f g, π(valid i f ⇒ p i f ⇒ p (and1 i) (f ∧ g))) →
(Π i f g, π(valid i g ⇒ p i g ⇒ p (and2 i) (f ∧ g))) →
(Π i f g, π(valid i f ⇒ p i f ⇒ p (or1 i) (f ∨ g))) →
(Π i f g, π(valid i g ⇒ p i g ⇒ p (or2 i) (f ∨ g))) →
(Π i f g, π(valid i f ⇒ p i f ⇒ p (imp1 i) (f ⇒ g))) →
(Π i f g, π(valid i g ⇒ p i g ⇒ p (imp2 i) (f ⇒ g))) →
Π i f, π(valid i f ⇒ p i f) ≔
begin
assume p ptop pall pex pand1 pand2 por1 por2 pimp1 pimp2; induction
// top
{ refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ptop }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
}
// all
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume a f hf v; apply pall i a f v; assume x; apply hi; refine (v x) }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
}
// ex
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply pex i a f v; assume x; apply hi; refine (v x) }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
}
// and1
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply pand1 i f g v (hi f v) }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
}
// and2
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply pand2 i f g v (hi g v) }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
}
// or1
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply por1 i f g v (hi f v) }
  { assume f g hf hg v; apply ⊥ₑ v }
}
// or2
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply por2 i f g v (hi g v) }
  { assume f g hf hg v; apply ⊥ₑ v }
}
// imp1
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply pimp1 i f g v (hi f v) }
}
// imp2
{ assume i hi; refine ind_Prop _ _ _ _ _ _ _
  { assume k v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume a f hf v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply ⊥ₑ v }
  { assume f g hf hg v; apply pimp2 i f g v (hi g v) }
}
end;

// skolemization of a particular existential

// /!\ WARNING: partial function defined on valid positions only
symbol skolem1: Pos → Prop → Prop;
symbol skolem1-: Pos → Prop → Prop;

rule skolem1 top (∃ $p) ↪ $p (ε $p)
with skolem1 (all $i) (∀ $p) ↪ `∀ x, skolem1 $i ($p x)
with skolem1 (and1 $i) ($p ∧ $q) ↪ skolem1 $i $p ∧ $q
with skolem1 (and2 $i) ($p ∧ $q) ↪ $p ∧ skolem1 $i $q
with skolem1 (or1 $i) ($p ∨ $q) ↪ skolem1 $i $p ∨ $q
with skolem1 (or2 $i) ($p ∨ $q) ↪ $p ∨ skolem1 $i $q
with skolem1 (imp1 $i) ($p ⇒ $q) ↪ skolem1- $i $p ⇒ $q
with skolem1 (imp2 $i) ($p ⇒ $q) ↪ $p ⇒ skolem1 $i $q

with skolem1- top (∀ $p) ↪ $p (ε $p)
with skolem1- (ex $i) (∃ $p) ↪ `∃ x, skolem1- $i ($p x)
with skolem1- (and1 $i) ($p ∧ $q) ↪ skolem1- $i $p ∧ $q
with skolem1- (and2 $i) ($p ∧ $q) ↪ $p ∧ skolem1- $i $q
with skolem1- (or1 $i) ($p ∨ $q) ↪ skolem1- $i $p ∨ $q
with skolem1- (or2 $i) ($p ∨ $q) ↪ $p ∨ skolem1- $i $q
with skolem1- (imp1 $i) ($p ⇒ $q) ↪ skolem1 $i $p ⇒ $q
with skolem1- (imp2 $i) ($p ⇒ $q) ↪ $p ⇒ skolem1- $i $q
;

assert ⊢ skolem1 (all top) A ≡ B;
assert ⊢ skolem1 (all(and2(all top))) B ≡ C;

// correctness proof

opaque symbol skolem1_correct i f: π(valid i f) → π f → π(skolem1 i f) ≔
begin
refine ind_valid (λ i f, f ⇒ skolem1 i f) _ _ _ _ _ _ _ _ _
{ assume a f h; apply εᵢ _ h }
{ assume i a f v IH h x; apply IH x (h x) }
{ admit }
{ assume i f g v IH h; apply ∧ᵢ { apply IH (∧ₑ₁ h) } { apply ∧ₑ₂ h } }
{ assume i f g v IH h; apply ∧ᵢ { apply ∧ₑ₁ h } { apply IH (∧ₑ₂ h) } }
{ assume i f g v IH h; apply ∨ₑ h { assume hf; apply ∨ᵢ₁ (IH hf) } { assume hg; apply ∨ᵢ₂ hg } }
{ assume i f g v IH h; apply ∨ₑ h { assume hf; apply ∨ᵢ₁ hf } { assume hg; apply ∨ᵢ₂ (IH hg) } }
{ assume i f g v IH h; admit }
{ assume i f g v IH h; admit }
end;
