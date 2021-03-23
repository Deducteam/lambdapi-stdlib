require open Stdlib.Set Stdlib.Logic;

// Type of natural numbers

inductive ℕ : TYPE ≔
| zero : ℕ
| suc : ℕ → ℕ ;

constant symbol nat : Set;

rule τ nat ↪ ℕ;

// Enabling the use of decimal notation

builtin "0"  ≔ zero;
builtin "+1" ≔ suc;

assert ⊢ 42 : ℕ;

// is_0 predicate

symbol is_0 : ℕ → Prop;

rule is_0 0 ↪ ⊤
with is_0 (suc _) ↪ ⊥;

// 0 ≠ 1

opaque symbol suc_is_not_zero n : π (suc n ≠ 0) ≔
begin
  assume n h;
  refine eq_ind h is_0 top;
end;

// Addition

symbol + : ℕ → ℕ → ℕ;

notation + infix left 6;

assert x y z ⊢ x + y + z ≡ (x + y) + z; // check associativity

rule 0 + $y ↪ $y
with suc $x + $y ↪ suc ($x + $y);

// Addition is commutative

opaque symbol add0r x : π (x + 0 = x) ≔
begin
  induction;
  // case x = 0
  reflexivity;
  // case x = s x'
  assume x' h;
  simpl;
  rewrite h;
  reflexivity;
end;

rule $x + 0 ↪ $x;

opaque symbol addsr x y : π (x + suc y = suc (x + y)) ≔
begin
  induction;
  // case x = 0
  assume y;
  reflexivity;
  // case x = s x'
  assume x' h y;
  simpl;
  rewrite h;
  reflexivity;
end;

rule $x + suc $y ↪ suc ($x + $y);

opaque symbol add_com x y : π (x + y = y + x) ≔
begin
  induction;
  // case x = 0
  assume y;
  reflexivity;
  // case x = s x'
  simpl;
  assume x' h y;
  rewrite h;
  reflexivity;
end;

// Addition is associative

opaque symbol add_assoc x y z : π ((x + y) + z = x + (y + z)) ≔
begin
  induction;
  // case x = 0
  assume y z;
  reflexivity;
  // case x = s x'
  assume x' h y z;
  simpl;
  rewrite h;
  reflexivity;
end;

rule ($x + $y) + $z ↪ $x + ($y + $z);

// Multiplication

symbol × : ℕ → ℕ → ℕ; // \times

notation × infix left 7;

assert x y z ⊢ x + y × z ≡ x + (y × z); // check priorities

rule 0 × _  ↪ 0
with suc $x × $y ↪ $y + $x × $y;

// Multiplication is commutative

opaque symbol mul0r x : π (x × 0 = 0) ≔
begin
  induction;
  // case x = 0
  reflexivity;
  // case x = s x'
  assume x' h;
  apply h;
end;

rule _ × 0 ↪ 0;

opaque symbol mulsr x y : π (x × suc y = x × y + x) ≔
begin
  induction;
  // case x = 0
  assume y;
  reflexivity;
  // case x = s x'
  assume x' h y;
  simpl;
  rewrite h;
  reflexivity;
end;

rule $x × suc $y ↪ $x + $x × $y;

opaque symbol mul_com x y : π (x × y = y × x) ≔
begin
  induction;
  // case x = 0
  assume y;
  reflexivity;
  // case x = s x'
  assume x' h y;
  simpl;
  rewrite h;
  reflexivity;
end;

// Multiplication distributes over addition

opaque symbol mul_addl x y z : π ((x + y) × z = x × z + y × z) ≔
begin
  induction;
  // case x = 0
  assume y z;
  reflexivity;
  // case x = s x'
  assume x' h y z;
  simpl;
  rewrite h;
  reflexivity;
end;

rule ($x + $y) × $z ↪ $x × $z + $y × $z;

opaque symbol mul_addr x y z : π (z × (x + y) = z × x + z × y) ≔
begin
  assume x y z;
  rewrite mul_com;
  rewrite mul_addl;
  rewrite mul_com;
  rewrite [y × _]mul_com;
  reflexivity;
end;

rule $z × ($x + $y) ↪ $z × $x + $z × $y;

// Multiplication is associative

opaque symbol mul_assoc x y z : π ((x × y) × z = x × (y × z)) ≔
begin
  induction;
  // case x = 0
  assume y z;
  reflexivity;
  // case x = s x'
  assume x' h y z;
  simpl;
  rewrite h;
  reflexivity;
end;

rule ($x × $y) × $z ↪ $x × ($y × $z);
