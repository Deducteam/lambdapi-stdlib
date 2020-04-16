require open Stdlib.Set

// Type of propositions

constant symbol Prop : TYPE

// Interpretation of propositions in TYPE

set declared "π"

injective symbol π : Prop → TYPE

// Conjunction

constant symbol conj : Prop → Prop → Prop

set infix left 7 "∧" ≔ conj

constant symbol conj_intro p q : π p → π q → π (p ∧ q)
symbol conj_elim_left p q : π (p ∧ q) → π p
symbol conj_elim_right p q : π (p ∧ q) → π q

// Disjunction

constant symbol disj : Prop → Prop → Prop

set infix left 6 "∨" ≔ disj

constant symbol disj_intro_left p q : π p → π (p ∨ q)
constant symbol disj_intro_right p q : π q → π (p ∨ q)
symbol disj_elim p q r : π (p ∨ q) → (π p → π r) → (π q → π r) → π r

assert λx y z,x∨y∧z ≡ λx y z,x∨(y∧z) // check that propositions are parsed correctly
  
// False

set declared "⊥"

constant symbol ⊥ : Prop
constant symbol false_elim p : π ⊥ → π p

// Negation

set declared "¬"

constant symbol ¬ : Prop → Prop

rule π (¬ $p) ↪ π $p → π ⊥

// Universal quantification

constant symbol forall {a} : (τ a → Prop) → Prop

rule π (@forall $a $f) ↪ Πx:τ $a, π ($f x)

// Existential quantification

set declared "∃"

constant symbol ∃ {a} : (τ a → Prop) → Prop
constant symbol ex_intro {a} p (x:τ a) : π (p x) → π (∃ p)
symbol ex_elim {a} p q : π (∃ p) → (Πx:τ a, π (p x) → π q) → π q

// Leibniz equality

constant symbol eq {a} : τ a → τ a → Prop

set infix 1 "=" ≔ eq

constant symbol eq_refl {a} (x:τ a) : π (x = x)
constant symbol eq_ind {a} (x y:τ a) : π (x = y) → Πp, π (p y) → π (p x)

// Set builtins for the rewrite tactic

set builtin "P"     ≔ π
set builtin "T"     ≔ τ
set builtin "eq"    ≔ eq
set builtin "refl"  ≔ eq_refl
set builtin "eqind" ≔ eq_ind
set builtin "all"   ≔ forall

// Properties of Leibniz equality

theorem eq_sym {a} (x y:τ a) : π (x=y) → π (y=x)
proof
  assume a x y xy
  symmetry
  apply xy
qed
