require open Set

// Type of propositions

symbol const Prop : TYPE

// Interpretation of propositions in TYPE

symbol injective P : Prop ⇒ TYPE

// Conjunction

symbol const {|and|} : Prop ⇒ Prop ⇒ Prop

set infix left 7 "∧" ≔ {|and|}

symbol const and_intro p q : P p ⇒ P q ⇒ P (p ∧ q)
symbol and_elim_left p q : P (p ∧ q) ⇒ P p
symbol and_elim_right p q : P (p ∧ q) ⇒ P q

// Disjunction

symbol const or : Prop ⇒ Prop ⇒ Prop

set infix left 6 "∨" ≔ or

symbol const or_intro_left p q : P p ⇒ P (p ∨ q)
symbol const or_intro_right p q : P q ⇒ P (p ∨ q)
symbol or_elim p q r : P (p ∨ q) ⇒ (P p ⇒ P r) ⇒ (P q ⇒ P r) ⇒ P r

assert λx y z,x∨y∧z ≡ λx y z,x∨(y∧z) // check that propositions are parsed correctly
  
// False

set declared "⊥"

symbol const ⊥ : Prop
symbol const false_elim p : P ⊥ ⇒ P p

// Negation

set declared "¬"

symbol const ¬ : Prop ⇒ Prop

rule P (¬ &p) → P &p ⇒ P ⊥

// Universal quantification

symbol const all {a} : (S a ⇒ Prop) ⇒ Prop

rule P (@all &a &f) → ∀x:S &a, P (&f x)

// Existential quantification

set declared "∃"

symbol const ∃ {a} : (S a ⇒ Prop) ⇒ Prop
symbol const ex_intro {a} p (x:S a) : P (p x) ⇒ P (∃ p)
symbol ex_elim {a} p q : P (∃ p) ⇒ (∀x:S a, P (p x) ⇒ P q) ⇒ P q

// Leibniz equality

symbol const eq {a} : S a ⇒ S a ⇒ Prop

set infix 1 "=" ≔ eq

symbol const eq_refl {a} (x:S a) : P (x = x)
symbol const eq_ind {a} (x y:S a) : P (x = y) ⇒ ∀p, P (p y) ⇒ P (p x)

// Set builtins for the rewrite tactic

set builtin "P"     ≔ P
set builtin "T"     ≔ S
set builtin "eq"    ≔ eq
set builtin "refl"  ≔ eq_refl
set builtin "eqind" ≔ eq_ind
set builtin "all"   ≔ all

// Properties of Leibniz equality

theorem eq_sym {a} (x y:S a) : P (x=y) ⇒ P (y=x)
proof
  assume a x y xy
  symmetry
  apply xy
qed
