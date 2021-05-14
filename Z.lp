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

// Interaction of addition with opposite

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

// Interaction of succ and doubling functions

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

symbol double_succ x : π (double (x + 1) = succ_double x + 1)
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

symbol -_same z : π (z + ~ z = 0)
≔ begin
  induction;
  reflexivity;
  simplify; refine sub_same;
  simplify; refine sub_same;
end;

// Associativity

symbol sub_succ x y : π (sub (succ x) y = sub x y + 1)
≔ begin
  induction;
  assume x xrec; induction;
  assume y _;
  simplify; rewrite xrec; rewrite pred_double_succ;
  rewrite succ_double_carac; reflexivity;
  assume y _;
  simplify; rewrite xrec; rewrite double_succ;
  reflexivity;
  simplify; rewrite pos_pred_double_succ; reflexivity;

  assume x xrec; induction;
  assume y _; simplify; rewrite left succ_pred_double (sub x y);
  reflexivity;
  assume y _; simplify; rewrite succ_double_carac;
  reflexivity;
  simplify; rewrite succ_pos_pred_double; reflexivity;

  induction;
  induction; reflexivity; reflexivity; reflexivity;
  induction; reflexivity; reflexivity; reflexivity;
  reflexivity;
end;

symbol add_Zpos_succ x p : π (x + Zpos (succ p) = (x + Zpos p) + 1)
≔ begin
  induction;
  reflexivity;
  assume x p; simplify; rewrite add_succ_right; reflexivity;
  assume x p; simplify; rewrite sub_succ; reflexivity;
end;

symbol sub_add_Zpos a b c : π (sub a b + Zpos c = sub (add a c) b)
≔ begin
  assume a b c;
  refine ind_positive_peano (λ c, sub a b + Zpos c = sub (add a c) b) _ _ c;
  simplify; rewrite sub_succ; reflexivity;

  assume r rrec; rewrite add_Zpos_succ;
  rewrite rrec; rewrite add_succ_right; rewrite sub_succ;
  reflexivity;
end;

symbol sub_add_Zneg a b c : π (sub a b + Zneg c = sub a (add b c))
≔ begin
  assume a b c;
  rewrite left sub_opp (add b c) a;
  rewrite left sub_add_Zpos b a c;
  rewrite distr_~_+;
  rewrite sub_opp;
  reflexivity;
end;

symbol +_assoc x y z : π (x + y + z = x + (y + z))
≔ begin
  induction;
  reflexivity;

  assume x; induction; reflexivity;
  assume y; induction; reflexivity;
  // Zpos - Zpos - Zpos
  assume z; simplify; rewrite add_assoc; reflexivity;
  // Zpos - Zpos - Zneg
  assume z; simplify; rewrite +_com; rewrite sub_add_Zpos;
  rewrite add_com; reflexivity;

  assume y; induction; reflexivity;
  // Zpos - Zneg - Zpos
  assume z; simplify; rewrite sub_add_Zpos; rewrite +_com;
  rewrite sub_add_Zpos; rewrite add_com; reflexivity;
  // Zpos - Zneg - Zneg
  assume z; simplify; rewrite sub_add_Zneg; reflexivity;

  assume x; induction; reflexivity;
  assume y; induction; reflexivity;
  // Zneg - Zpos - Zpos
  assume z; simplify; rewrite sub_add_Zpos; reflexivity;
  // Zneg - Zpos - Zneg
  assume z; simplify; rewrite sub_add_Zneg; rewrite +_com;
  rewrite sub_add_Zneg; rewrite add_com; reflexivity;

  assume y; induction; reflexivity;
  // Zneg - Zneg - Zpos
  assume z; simplify; rewrite +_com; rewrite sub_add_Zneg;
  rewrite add_com; reflexivity;
  // Zneg - Zneg - Zneg
  assume z; simplify; rewrite add_assoc; reflexivity;
end;

// Comparison of integers

require open Stdlib.Comp;

symbol ≐ : ℤ → ℤ → comparison; // \doteq
notation ≐ infix 12;

rule Z0      ≐ Z0      ↪ Eq
with Z0      ≐ Zpos _  ↪ Lt
with Z0      ≐ Zneg _  ↪ Gt
with Zpos _  ≐ Z0      ↪ Gt
with Zpos $p ≐ Zpos $q ↪ compare $p $q
with Zpos _  ≐ Zneg _  ↪ Gt
with Zneg _  ≐ Z0      ↪ Lt
with Zneg _  ≐ Zpos _  ↪ Lt
with Zneg $p ≐ Zneg $q ↪ compare $q $p;

// ≐ decides the equality of integers

symbol ≐_decides x y : π (x ≐ y = Eq ⇒ x = y)
≔ begin
  induction;
  induction; reflexivity;
  assume y H; apply ⊥ₑ; refine discr_Lt_Eq H;
  assume y H; apply ⊥ₑ; refine discr_Gt_Eq H;
  assume x; induction;
  assume H; apply ⊥ₑ; refine discr_Gt_Eq H;
  assume y H; rewrite compare_decides x y H; reflexivity;
  assume y H; apply ⊥ₑ; refine discr_Gt_Eq H;
  assume x; induction;
  assume H; apply ⊥ₑ; refine discr_Lt_Eq H;
  assume y H; apply ⊥ₑ; refine discr_Lt_Eq H;
  assume y H; rewrite compare_decides y x H; reflexivity;
end;

// Commutative properties of ≐

symbol ≐_com x y : π (x ≐ y = CompOpp (y ≐ x))
≔ begin
  induction;
  induction; reflexivity; reflexivity; reflexivity;

  assume x; induction; reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
  reflexivity;

  assume x; induction; reflexivity;
  reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
end;

symbol ≐_opp x y : π (~ x ≐ ~ y = CompOpp (x ≐ y))
≔ begin
  induction;
  induction; reflexivity; reflexivity; reflexivity;

  assume x; induction; reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
  reflexivity;

  assume x; induction; reflexivity;
  reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
end;

// ≐ with 0

symbol ≐_double x : π ((double x ≐ 0) = (x ≐ 0))
≔ begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_pred_double x :
  π (pred_double x ≐ 0 = comparison_case (x ≐ 0) Lt Lt Gt)
≔ begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_succ_double x :
  π (succ_double x ≐ 0 = comparison_case (x ≐ 0) Gt Lt Gt)
≔ begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_pos_sub x y : π ((sub x y ≐ 0) = compare x y)
≔ begin
  induction;
  assume x xrec; induction;
  assume y _; simplify; rewrite ≐_double; refine xrec y;
  assume y _; simplify; rewrite ≐_succ_double; rewrite xrec;
  rewrite compare_Gt; reflexivity;
  reflexivity;

  assume x xrec; induction;
  assume y _; simplify; rewrite ≐_pred_double; rewrite xrec;
  rewrite compare_Lt; reflexivity;
  assume y _; simplify; rewrite ≐_double; refine xrec y;
  reflexivity;

  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_sub x y : π ((x ≐ y) = (x - y ≐ 0))
≔ begin
  induction;
  induction; reflexivity; reflexivity; reflexivity;

  assume x; induction; reflexivity;
  assume y; simplify; rewrite ≐_pos_sub; reflexivity;
  reflexivity;

  assume x; induction; reflexivity;
  reflexivity;
  assume y; simplify; rewrite ≐_pos_sub; reflexivity;
end;

// Compatibility with addition

symbol ≐_compat_add x y z : π ((x ≐ y) = (x + z ≐ y + z))
≔ begin
  assume x y z;
  rewrite ≐_sub;
  rewrite [x in _ = x] ≐_sub;
  simplify; rewrite distr_~_+;
  rewrite [~ y + ~ z] +_com;
  rewrite +_assoc; rewrite left +_assoc z (~ z) (~ y);
  rewrite -_same z; reflexivity;
end;
