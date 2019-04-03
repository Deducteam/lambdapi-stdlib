set flag "print_implicits" off

require open Set Logic

// Type of natural numbers

symbol const nat : Set

definition N ≔ S nat

symbol const zero : N
symbol const succ : N ⇒ N

// Enabling builtin natural number literals

set builtin "0"  ≔ zero
set builtin "+1" ≔ succ

assert 42 : N

// Induction principle

symbol nat_ind p : P (p 0) ⇒ (∀x, P (p x) ⇒ P (p (succ x))) ⇒ ∀x, P (p x)

// Addition

symbol add : N ⇒ N ⇒ N

set infix left 6 "+" ≔ add

assert λx y z,x+y=z : ∀x y z,Prop // check that x+y=z is parsed as expected

rule 0       + &y → &y
 and succ &x + &y → succ (&x + &y)

// Addition is commutative

theorem add0r x : P (x + 0 = x)
proof
  refine nat_ind _ _ _
  // case x = 0
  simpl
  reflexivity
  // case x = s x'
  intro x' h
  simpl
  rewrite h
  reflexivity
qed

rule &x + 0 → &x

theorem addsr x y : P (x + succ y = succ (x + y))
proof
  refine nat_ind _ _ _
  // case x = 0
  simpl
  intro y reflexivity //FIXME: remove intro y
  // case x = s x'
  intro x' h y
  simpl
  rewrite h
  reflexivity
qed

rule &x + (succ &y) → succ (&x + &y)

theorem add_com x y : P (x+y = y+x)
proof
  refine nat_ind _ _ _
  // case x = 0
  simpl
  intro y reflexivity //FIXME: remove intro y
  // case x = s x'
  simpl
  intro x' h y
  rewrite h
  reflexivity
qed

// Addition is associative

theorem add_assoc x y z : P ((x+y)+z = x+(y+z))
proof
  set debug +ts
  refine nat_ind _ _ _
  // case x = 0
  simpl
  //reflexivity
qed

// Multiplication

symbol mul : N ⇒ N ⇒ N

set infix left 7 "×" ≔ mul

assert λx y z,x+y×z ≡ λx y z,x+(y×z)

rule 0         × _         → 0
 and (succ &x) × &y        → &y + &x × &y
 and _         × 0         → 0
 and &x        × (succ &y) → &x + &x × &y
