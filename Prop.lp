// Propositional logic

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// Interpretation of propositions in TYPE

injective symbol π : Prop → TYPE;

builtin "P" ≔ π;

// True

constant symbol ⊤ : Prop;

constant symbol top : π ⊤;

// False

constant symbol ⊥ : Prop;

constant symbol ⊥ₑ p : π ⊥ → π p;

// Conjunction

constant symbol ∧ : Prop → Prop → Prop; // \wedge

notation ∧ infix left 7;

constant symbol ∧ᵢ p q : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ p q : π (p ∧ q) → π p;
symbol ∧ₑ₂ p q : π (p ∧ q) → π q;

// Disjunction

constant symbol ∨ : Prop → Prop → Prop; // \vee

notation ∨ infix left 6;

constant symbol ∨ᵢ₁ p q : π p → π (p ∨ q);
constant symbol ∨ᵢ₂ p q : π q → π (p ∨ q);
symbol ∨ₑ p q r : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

// Implication

constant symbol ⇒ : Prop → Prop → Prop; // =>

notation ⇒ infix right 5;

symbol ⇒ₑ p q : π(p) → π (p ⇒ q) → π(q);

rule π ($p ⇒ $q) ↪ π $p → π $q;

// Reflexion of ⇒
opaque symbol ⇒_refl p : π (p ⇒ p) ≔
begin
  assume p; simplify; assume P; apply P;
end;

// Transitivity of ⇒
opaque symbol ⇒_trans p q r : π (p ⇒ q) → π (q ⇒ r) → π (p ⇒ r) ≔
begin
  assume p q r h1 h2;
  simplify;
  assume P;
  have Q:π (q) { apply ⇒ₑ _ _ P h1; };
  apply ⇒ₑ _ _ Q h2;
end;

//Equivalence

symbol ⇔ : Prop → Prop → Prop ≔ λ p, λ q, (p ⇒ q) ∧ (q ⇒ p);

notation ⇔ infix right 5;

opaque symbol ⇔ᵢ p q : π (p ⇒ q) → π (q ⇒ p) → π (p ⇔ q) ≔
begin
  assume p q d r;
  apply ∧ᵢ _ _ d r;
end;

opaque symbol ⇔ₑ₁ p q : π (p ⇔ q) → π (p ⇒ q) ≔
begin
  assume p q eq;
  apply ∧ₑ₁ _ _ eq;
end;

opaque symbol ⇔ₑ₂ p q : π (p ⇔ q) → π (q ⇒ p) ≔
begin
  assume p q eq;
  apply ∧ₑ₂ _ _ eq;
end;

//Modus ponens for ⇔
opaque symbol ⇔ₑ p q : π (p) → π (p ⇔ q) → π (q) ≔
begin
  assume p q P thm;
  have t:π (p ⇒ q) { apply ∧ₑ₁ _ _ thm; };
  apply ⇒ₑ _ _ P t;
end;

opaque symbol ⇔ₑₑ p q : π (q) → π (p ⇔ q) → π (p) ≔
begin
  assume p q Q thm;
  have t:π (q ⇒ p) { apply ∧ₑ₂ _ _ thm; };
  apply ⇒ₑ _ _ Q t;
end;

// ⇔ is an equivalence relation
opaque symbol ⇔_refl p : π (p ⇔ p) ≔
begin
  assume p;
  apply ∧ᵢ {
    refine ⇒_refl p;
  } {
    refine ⇒_refl p;
  };
end;

opaque symbol ⇔_sym p q : π (p ⇔ q) → π (q ⇔ p) ≔
begin
  assume p q h;
  have t1:π (p ⇒ q) { apply ∧ₑ₁ _ _ h; };
  have t2:π (q ⇒ p) { apply ∧ₑ₂ _ _ h; };
  apply ∧ᵢ { refine t2; } { refine t1; };
end;

opaque symbol ⇔_trans p q r : π (p ⇔ q) → π (q ⇔ r) → π (p ⇔ r) ≔
begin
  assume p q r h1 h2;
  apply ∧ᵢ {
    simplify; assume P;
    have Q: π (q) { apply ⇔ₑ _ _ P h1; };
    apply ⇔ₑ _ _ Q h2;
  } {
    simplify; assume R;
    have Q: π (q) { apply ⇔ₑₑ _ _ R h2; };
    apply ⇔ₑₑ _ _ Q h1;
  };
end;

// Negation

symbol ¬ p ≔ p ⇒ ⊥;
