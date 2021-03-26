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

constant symbol false_elim p : π ⊥ → π p;

// Conjunction

constant symbol ∧ : Prop → Prop → Prop; // \wedge

notation ∧ infix left 7;

constant symbol conj_intro p q : π p → π q → π (p ∧ q);
symbol conj_elim_left p q : π (p ∧ q) → π p;
symbol conj_elim_right p q : π (p ∧ q) → π q;

// Disjunction

constant symbol ∨ : Prop → Prop → Prop; // \vee

notation ∨ infix left 6;

constant symbol disj_intro_left p q : π p → π (p ∨ q);
constant symbol disj_intro_right p q : π q → π (p ∨ q);
symbol disj_elim p q r : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

// Implication

constant symbol ⇒ : Prop → Prop → Prop; // =>

notation ⇒ infix left 5;

rule π ($p ⇒ $q) ↪ π $p → π $q;

// Negation

symbol ¬ p ≔ p ⇒ ⊥;
