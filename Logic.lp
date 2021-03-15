require open Stdlib.Set;

// Type of propositions

constant symbol prop : Set;

symbol Prop ≔ τ prop;

builtin "Prop" ≔ Prop;

// Interpretation of propositions in TYPE

injective symbol π : Prop → TYPE;

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

// Universal quantification

constant symbol ∀ {a} : (τ a → Prop) → Prop;

notation ∀ quantifier;

rule π (∀ $f) ↪ Π x, π ($f x);
/*verbose 3;
flag "print_domains" on;
unif_rule π $p ≡ Π x:$t, $u[x]
↪ [ Π x:$t, $u[x] ≡ Π x:τ $a, π $q[x];
    $p ≡ `∀ x:$t, $q[x] ];
verbose 1;*/

// Existential quantification

constant symbol ∃ {a} : (τ a → Prop) → Prop;

notation ∃ quantifier;

constant symbol ex_intro {a} p (x:τ a) : π (p x) → π (∃ p);
symbol ex_elim {a} p q : π (∃ p) → (Π x:τ a, π (p x) → π q) → π q;

// Leibniz equality

constant symbol = {a} : τ a → τ a → Prop;

notation = infix 1;

constant symbol eq_refl {a} (x:τ a) : π (x = x);
constant symbol eq_ind {a} {x y:τ a} : π (x = y) → Π p, π (p y) → π (p x);

// inequality

symbol ≠ {a} (x y : τ a) ≔ ¬ (x = y); // \neq

notation ≠ infix 1;

// Set builtins for the rewrite tactic

builtin "P"     ≔ π;
builtin "T"     ≔ τ;
builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ eq_ind;
builtin "all"   ≔ ∀;

// Properties of Leibniz equality

opaque symbol eq_sym {a} (x y:τ a) : π (x = y) → π (y = x) ≔
begin
  assume a x y xy;
  symmetry;
  apply xy;
end;
