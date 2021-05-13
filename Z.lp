// Binary integers

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Pos;

inductive ℤ : TYPE ≔ // \BbbZ
| Z0 : ℤ
| Zpos : positive → ℤ
| Zneg : positive → ℤ;

// set code for ℤ

constant symbol int : Set;

rule τ int ↪ ℤ;

// Injections in Prop

symbol is_Z0 : ℤ → Prop;

rule is_Z0 Z0       ↪ ⊤
with is_Z0 (Zpos _) ↪ ⊥
with is_Z0 (Zneg _) ↪ ⊥;

symbol is_Zpos : ℤ → Prop;

rule is_Zpos Z0       ↪ ⊥
with is_Zpos (Zpos _) ↪ ⊤
with is_Zpos (Zneg _) ↪ ⊥;

symbol is_Zneg : ℤ → Prop;

rule is_Zneg Z0       ↪ ⊥
with is_Zneg (Zpos _) ↪ ⊥
with is_Zneg (Zneg _) ↪ ⊤;

// Discriminate constructors

symbol discr_Zpos_Z0 p : π (Zpos p ≠ Z0)
≔ begin
  assume p H;
  have f : π (is_Zpos Z0);
  rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

symbol discr_Zneg_Z0 p : π (Zneg p ≠ Z0)
≔ begin
  assume p H;
  have f : π (is_Zneg Z0);
  rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

symbol discr_Zpos_Zneg p q : π (Zpos p ≠ Zneg q)
≔ begin
  assume p q H;
  have f : π (is_Zpos (Zneg q));
  rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

// Unary opposite

symbol ~ : ℤ → ℤ;
notation ~ prefix 24;

rule ~ Z0 ↪ Z0
with ~ (Zpos $p) ↪ Zneg $p
with ~ (Zneg $p) ↪ Zpos $p;

symbol ~_idem z : π (~ ~ z = z)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

// Doubling functions

symbol double : ℤ → ℤ;

rule double Z0 ↪ Z0
with double (Zpos $p) ↪ Zpos (xO $p)
with double (Zneg $p) ↪ Zneg (xO $p);

symbol succ_double : ℤ → ℤ;

rule succ_double Z0 ↪ Zpos xH
with succ_double (Zpos $p) ↪ Zpos (xI $p)
with succ_double (Zneg $p) ↪ Zneg (pos_pred_double $p);

symbol pred_double : ℤ → ℤ;

rule pred_double Z0 ↪ Zneg xH
with pred_double (Zpos $p) ↪ Zpos (pos_pred_double $p)
with pred_double (Zneg $p) ↪ Zneg (xI $p);

// Interaction of opp and doubling functions

symbol double_opp z : π (double (~ z) = ~ double z)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol succ_double_opp z : π (succ_double (~ z) = ~ pred_double z)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pred_double_opp z : π (pred_double (~ z) = ~ succ_double z)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

// Binary negation on positive

symbol sub : positive → positive → ℤ;

rule sub (xI $p) (xI $q) ↪ double (sub $p $q)
with sub (xI $p) (xO $q) ↪ succ_double (sub $p $q)
with sub (xI $p) xH      ↪ Zpos (xO $p)
with sub (xO $p) (xI $q) ↪ pred_double (sub $p $q)
with sub (xO $p) (xO $q) ↪ double (sub $p $q)
with sub (xO $p) xH      ↪ Zpos (pos_pred_double $p)
with sub xH      (xI $q) ↪ Zneg (xO $q)
with sub xH      (xO $q) ↪ Zneg (pos_pred_double $q)
with sub xH       xH     ↪ Z0;


symbol sub_same z : π (sub z z = Z0)
≔ begin
  induction;
  assume x xrec;
  simplify; rewrite xrec; reflexivity;
  assume x xrec;
  simplify; rewrite xrec; reflexivity;
  reflexivity;
end;

symbol sub_opp x y : π (~ sub x y = sub y x)
≔ begin
  induction;
  assume x xrec; induction;
  assume y _; simplify; rewrite left xrec y;
  rewrite double_opp; reflexivity;
  assume y _; simplify; rewrite left xrec y;
  rewrite pred_double_opp; reflexivity;
  reflexivity;

  assume x xrec; induction;
  assume y _; simplify; rewrite left xrec y;
  rewrite succ_double_opp; reflexivity;
  assume y _; simplify; rewrite left xrec y;
  rewrite double_opp; reflexivity;
  reflexivity;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;


// Addition of integers

symbol + : ℤ → ℤ → ℤ;
notation + infix left 20;

rule Z0      + $y      ↪ $y
with $x      + Z0      ↪ $x
with Zpos $x + Zpos $y ↪ Zpos (add $x $y)
with Zpos $x + Zneg $y ↪ sub $x $y
with Zneg $x + Zpos $y ↪ sub $y $x
with Zneg $x + Zneg $y ↪ Zneg (add $x $y);

symbol +1 x ≔ x + Zpos xH;

builtin "0" ≔ Z0;
builtin "+1" ≔ +1;

// Interaction with opposite

symbol distr_~_+ x y : π (~ (x + y) = ~ x + ~ y)
≔ begin
  induction;
  reflexivity;
  assume x; induction;
  reflexivity;
  reflexivity;
  assume y; simplify; rewrite sub_opp; reflexivity;

  assume x; induction;
  reflexivity;
  assume y; simplify; rewrite sub_opp; reflexivity;
  reflexivity;
end;

// Commutativity of addition

symbol +_com x y : π (x + y = y + x)
≔ begin
  induction;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;

  assume x;
  induction;
  reflexivity;
  assume y; simplify; rewrite add_com; reflexivity;
  reflexivity;

  assume x;
  induction;
  reflexivity;
  reflexivity;
  assume y; simplify; rewrite add_com; reflexivity;
end;


symbol pred_double_succ x : π (pred_double (x + 1) = succ_double x)
≔ begin
  induction;
  reflexivity;
  assume x; simplify; rewrite pos_pred_double_succ; reflexivity;
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol succ_pred_double x : π (pred_double x + 1 = double x)
≔ begin
  induction;
  reflexivity;
  assume x; simplify; rewrite succ_pos_pred_double; reflexivity;
  reflexivity;
end;

symbol succ_double_carac x : π (succ_double x = double x + 1)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol double_succ x : π (double (x + 1) = double x + 2)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

// Negation

symbol - x y ≔ x + ~ y;
notation - infix left 20;

symbol +_same z : π (z - z = 0)
≔ begin
  induction;
  reflexivity;
  simplify; refine sub_same;
  simplify; refine sub_same;
end;

