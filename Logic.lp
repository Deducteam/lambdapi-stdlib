require open Stdlib.Set;

// Type of propositions

constant symbol prop : Set;

symbol Prop ≔ τ prop;

set builtin "Prop" ≔ Prop;

// Interpretation of propositions in TYPE

injective symbol π : Prop → TYPE;

// True

constant symbol ⊤ : Prop;

constant symbol top : π ⊤;

// False

constant symbol ⊥ : Prop;

constant symbol false_elim p : π ⊥ → π p;

// Negation

constant symbol ¬ : Prop → Prop;

rule π (¬ $p) ↪ π $p → π ⊥;

// Conjunction

constant symbol conj : Prop → Prop → Prop;

set infix left 7 "∧" ≔ conj;

constant symbol conj_intro p q : π p → π q → π (p ∧ q);
symbol conj_elim_left p q : π (p ∧ q) → π p;
symbol conj_elim_right p q : π (p ∧ q) → π q;

// Disjunction

constant symbol disj : Prop → Prop → Prop;

set infix left 6 "∨" ≔ disj;

constant symbol disj_intro_left p q : π p → π (p ∨ q);
constant symbol disj_intro_right p q : π q → π (p ∨ q);
symbol disj_elim p q r : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

// Implication

constant symbol impl : Prop → Prop → Prop;

set infix left 5 "⇒" ≔ impl;

rule π ($p ⇒ $q) ↪ π $p → π $q;

// Universal quantification

constant symbol ∀ {a} : (τ a → Prop) → Prop;

set quantifier ∀;

rule π (∀ $f) ↪ Π x, π ($f x);
//set unif_rule π $p ≡ Π x, π $q[x] ↪ [ $p ≡ `∀ x, $q[x] ];

// Existential quantification

constant symbol ∃ {a} : (τ a → Prop) → Prop;

set quantifier ∃;

constant symbol ex_intro {a} p (x:τ a) : π (p x) → π (∃ p);
symbol ex_elim {a} p q : π (∃ p) → (Π x:τ a, π (p x) → π q) → π q;

// Leibniz equality

constant symbol eq {a} : τ a → τ a → Prop;

set infix 1 "=" ≔ eq;

constant symbol eq_refl {a} (x:τ a) : π (x = x);
constant symbol eq_ind {a} {x y:τ a} : π (x = y) → Π p, π (p y) → π (p x);

// inequality

symbol neq {a} (x y : τ a) ≔ ¬ (x = y);

set infix 1 "≠" ≔ neq;

// Set builtins for the rewrite tactic

set builtin "P"     ≔ π;
set builtin "T"     ≔ τ;
set builtin "eq"    ≔ eq;
set builtin "refl"  ≔ eq_refl;
set builtin "eqind" ≔ eq_ind;
set builtin "all"   ≔ ∀;

// Properties of Leibniz equality

opaque symbol eq_sym {a} (x y:τ a) : π (x = y) → π (y = x) ≔
begin
  assume a x y xy;
  symmetry;
  apply xy;
end;
