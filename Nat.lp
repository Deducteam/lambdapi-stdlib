require open Stdlib.Set Stdlib.Logic

// Type of natural numbers

constant symbol nat : Set

set declared "ℕ"

definition ℕ ≔ τ nat

constant symbol zero : ℕ
constant symbol suc : ℕ → ℕ

// Enabling builtin natural number literals

set builtin "0"  ≔ zero
set builtin "+1" ≔ suc

assert 42 : ℕ // example

// Induction principle on propositions

symbol nat_ind p : π (p 0) → (Πx, π (p x) → π (p (suc x))) → Πx, π (p x)

// is_0 predicate

symbol is_0 : ℕ → Prop

rule is_0 0 ↪ ⊤
with is_0 (suc _) ↪ ⊥

// 0 ≠ 1

theorem suc_is_not_zero n : π (suc n ≠ 0)

proof
  assume n h
  refine eq_ind h is_0 top
qed

// Addition

symbol add : ℕ → ℕ → ℕ

set infix left 6 "+" ≔ add

assert λx y z,x+y+z ≡ λx y z,(x+y)+z // check that x+y=z is parsed correctly

rule 0 + $y ↪ $y
with suc $x + $y ↪ suc ($x + $y)

// Addition is commutative

theorem add0r x : π (x + 0 = x)
proof
  refine nat_ind _ _ _
  // case x = 0
  reflexivity
  // case x = s x'
  assume x' h
  simpl
  rewrite h
  reflexivity
qed

rule $x + 0 ↪ $x

theorem addsr x y : π (x + suc y = suc (x + y))
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  assume x' h y
  simpl
  rewrite h
  reflexivity
qed

rule $x + suc $y ↪ suc ($x + $y)

theorem add_com x y : π (x+y = y+x)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  simpl
  assume x' h y
  rewrite h
  reflexivity
qed

// Addition is associative

theorem add_assoc x y z : π ((x+y)+z = x+(y+z))
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y z
  reflexivity
  // case x = s x'
  assume x' h y z
  simpl
  rewrite h
  reflexivity
qed

rule ($x + $y) + $z ↪ $x + ($y + $z)

// Multiplication

symbol mul : ℕ → ℕ → ℕ

set infix left 7 "×" ≔ mul

assert λx y z,x+y×z ≡ λx y z,x+(y×z) // check that x+y×z is parsed correctly

rule 0 × _  ↪ 0
with suc $x × $y ↪ $y + $x × $y

// Multiplication is commutative

theorem mul0r x : π (x × 0 = 0)
proof
  refine nat_ind _ _ _
  // case x = 0
  reflexivity
  // case x = s x'
  assume x' h
  apply h
qed

rule _ × 0 ↪ 0

theorem mulsr x y : π (x × suc y = x × y + x)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  assume x' h y
  simpl
  rewrite h
  reflexivity
qed

rule $x × suc $y ↪ $x + $x × $y

theorem mul_com x y : π (x × y = y × x)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  assume x' h y
  simpl
  rewrite h
  reflexivity
qed

// Multiplication distributes over addition

theorem mul_addl x y z : π ((x+y)×z = x×z+y×z)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y z
  reflexivity
  // case x = s x'
  assume x' h y z
  simpl
  rewrite h
  reflexivity
qed

rule ($x + $y) × $z ↪ $x × $z + $y × $z

theorem mul_addr x y z : π (z×(x+y) = z×x+z×y)
proof
  assume x y z
  rewrite mul_com
  rewrite mul_addl
  rewrite mul_com
  rewrite [y×_]mul_com
  reflexivity
qed

rule $z × ($x + $y) ↪ $z × $x + $z × $y

// Multiplication is associative

theorem mul_assoc x y z : π ((x × y) × z = x × (y × z))
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y z
  reflexivity
  // case x = s x'
  assume x' h y z
  simpl
  rewrite h
  reflexivity
qed

rule ($x × $y) × $z ↪ $x × ($y × $z)
