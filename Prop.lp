// Propositional logic

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// Interpretation of propositions in TYPE

injective symbol π : Prop → TYPE; // `p

builtin "P" ≔ π;

// True

constant symbol ⊤ : Prop; // \top

constant symbol top : π ⊤;

// False

constant symbol ⊥ : Prop; // \bot

constant symbol ⊥ₑ p : π ⊥ → π p; // \bot__e

// Conjunction

constant symbol ∧ : Prop → Prop → Prop; // \wedge

notation ∧ infix left 7;

constant symbol ∧ᵢ p q : π p → π q → π (p ∧ q); // \wedge__i
symbol ∧ₑ₁ p q : π (p ∧ q) → π p; // \wedge__e__1
symbol ∧ₑ₂ p q : π (p ∧ q) → π q; // \wedge__e__2

// Disjunction

constant symbol ∨ : Prop → Prop → Prop; // \vee

notation ∨ infix left 6;

constant symbol ∨ᵢ₁ p q : π p → π (p ∨ q); // \vee__i__1
constant symbol ∨ᵢ₂ p q : π q → π (p ∨ q); // \vee__i__2
symbol ∨ₑ p q r : π (p ∨ q) → (π p → π r) → (π q → π r) → π r; // \vee__e

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

// Implication

constant symbol ⇒ : Prop → Prop → Prop; // =>

notation ⇒ infix right 5;

rule π ($p ⇒ $q) ↪ π $p → π $q;

// Negation

symbol ¬ p ≔ p ⇒ ⊥; // \neg
