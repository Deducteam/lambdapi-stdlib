// Propositional logic

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// interpretation of propositions in TYPE

injective symbol π : Prop → TYPE; // `p

builtin "P" ≔ π;

// true

constant symbol ⊤ : Prop; // \top

constant symbol top : π ⊤;

// false

constant symbol ⊥ : Prop; // \bot

constant symbol ⊥ₑ [p] : π ⊥ → π p;

// implication

constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 5; // =>

rule π ($p ⇒ $q) ↪ π $p → π $q;

symbol fold_⇒ [p q] : π (p ⇒ q) → π p → π q ≔
begin
  assume p q pq h; apply pq h;
end;

// negation

symbol ¬ p ≔ p ⇒ ⊥; // ~~ or \neg

// conjunction

constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix left 7; // /\ or \wedge

constant symbol ∧ᵢ [p q] : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ [p q] : π (p ∧ q) → π p;
symbol ∧ₑ₂ [p q] : π (p ∧ q) → π q;

// disjunction

constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix left 6; // \/ or \vee

constant symbol ∨ᵢ₁ [p q] : π p → π (p ∨ q);
constant symbol ∨ᵢ₂ [p q] : π q → π (p ∨ q);
symbol ∨ₑ [p q r] : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

// equivalence

symbol ⇔ p q ≔ (p ⇒ q) ∧ (q ⇒ p); notation ⇔ infix right 5;

opaque symbol ⇔_refl [p] : π (p ⇔ p) ≔
begin
  assume p; apply ∧ᵢ { assume h; apply h } { assume h; apply h }
end;

opaque symbol ⇔_sym [p q] : π (p ⇔ q) → π (q ⇔ p) ≔
begin
  assume p q h; apply ∧ᵢ { apply ∧ₑ₂ h } { apply ∧ₑ₁ h };
end;

opaque symbol ⇔_trans p q r : π (p ⇔ q) → π (q ⇔ r) → π (p ⇔ r) ≔
begin
  assume p q r epq eqr; apply ∧ᵢ
    { assume hp; apply ∧ₑ₁ eqr _; apply ∧ₑ₁ epq hp }
    { assume hr; apply ∧ₑ₂ epq _; apply ∧ₑ₂ eqr hr }
end;
