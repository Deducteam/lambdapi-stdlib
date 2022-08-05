// Booleans

require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.FOL Blanqui.Lib.Eq;

inductive 𝔹 : TYPE ≔
| true : 𝔹
| false : 𝔹;

// set code for 𝔹

constant symbol bool : Set;

rule τ bool ↪ 𝔹;

//Some useful predicates
symbol istrue : 𝔹 → Prop;

rule istrue true ↪ ⊤
with istrue false ↪ ⊥;

symbol boolification : Prop → 𝔹;

rule boolification ⊤ ↪ true
with boolification ⊥ ↪ false;

// 𝔹oolean not

symbol not : 𝔹 → 𝔹;

rule not true  ↪ false
with not false ↪ true;

// 𝔹oolean or

symbol or : 𝔹 → 𝔹 → 𝔹;

notation or infix left 6;

rule true  or _     ↪ true
with _     or true  ↪ true
with false or $b    ↪ $b
with $b    or false ↪ $b;

symbol or_i1 p q : π (istrue p) → π (istrue (p or q));
symbol or_i2 p q : π (istrue q) → π (istrue (p or q));

opaque symbol orC p q : π ((p or q) = (q or p)) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

opaque symbol orA p q r : π (((p or q) or r) = (p or (q or r))) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

// 𝔹oolean and

symbol and : 𝔹 → 𝔹 → 𝔹;

notation and infix left 7;

rule true  and $b    ↪ $b
with $b    and true  ↪ $b
with false and _     ↪ false
with _     and false ↪ false;

symbol and_e1 p q : π (istrue (p and q)) → π (istrue p); 
symbol and_e2 p q : π (istrue (p and q)) → π (istrue q); 

// Conditional

symbol if : 𝔹 → Π [a], τ a → τ a → τ a;

rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;

// Induction principle with hypothesis

opaque symbol dis_B : Π b:𝔹, π (b = true ∨ b = false) ≔
begin
  induction
  { apply ∨ᵢ₁ (true = true) (true = false); reflexivity; }
  { apply ∨ᵢ₂ (false = true) (false = false); reflexivity; }
end;

opaque symbol ind_B : Π P:(𝔹 → Prop), Π b:𝔹, (π (b = true) → π (P b)) → (π (b = false) → π (P b)) → π (P b) ≔
begin
  assume P b ht hf;
  refine ∨ₑ (b = true) (b = false) (P b) (dis_B b) ht hf;
end;