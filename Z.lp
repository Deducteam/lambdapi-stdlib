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

symbol discr_Zpos_Z0 p : π (Zpos p ≠ Z0) ≔
begin
  assume p H;
  have f : π (is_Zpos Z0); rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

symbol discr_Zneg_Z0 p : π (Zneg p ≠ Z0) ≔
begin
  assume p H;
  have f : π (is_Zneg Z0); rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

symbol discr_Zpos_Zneg p q : π (Zpos p ≠ Zneg q) ≔
begin
  assume p q H;
  have f : π (is_Zpos (Zneg q)); rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

// Unary opposite

symbol ~ : ℤ → ℤ;
notation ~ prefix 24;

rule ~ Z0 ↪ Z0
with ~ (Zpos $p) ↪ Zneg $p
with ~ (Zneg $p) ↪ Zpos $p;

symbol ~_idem z : π (~ ~ z = z) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
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

symbol double_opp z : π (double (~ z) = ~ double z) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol succ_double_opp z : π (succ_double (~ z) = ~ pred_double z) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol pred_double_opp z : π (pred_double (~ z) = ~ succ_double z) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
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

symbol sub_same z : π (sub z z = Z0) ≔
begin
  induction;
  assume x xrec; simplify; rewrite xrec; reflexivity;
  assume x xrec; simplify; rewrite xrec; reflexivity;
  reflexivity;
end;

symbol sub_opp x y : π (~ sub x y = sub y x) ≔
begin
  induction;
  // case xI
  assume x xrec; induction;
  assume y _; simplify; rewrite left xrec y; rewrite double_opp; reflexivity;
  assume y _; simplify; rewrite left xrec y; rewrite pred_double_opp; reflexivity;
  reflexivity;
  // case xO
  assume x xrec; induction;
  assume y _; simplify; rewrite left xrec y; rewrite succ_double_opp; reflexivity;
  assume y _; simplify; rewrite left xrec y; rewrite double_opp; reflexivity;
  reflexivity;
  // case xH
  induction; reflexivity; reflexivity; reflexivity;
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

symbol distr_~_+ x y : π (~ (x + y) = ~ x + ~ y) ≔
begin
  induction;
  // case Z0
  reflexivity;
  // case Zpos
  assume x; induction;
  reflexivity;
  reflexivity;
  assume y; simplify; rewrite sub_opp; reflexivity;
  // case Zneg
  assume x; induction;
  reflexivity;
  assume y; simplify; rewrite sub_opp; reflexivity;
  reflexivity;
end;

// Commutativity of addition

symbol +_com x y : π (x + y = y + x) ≔
begin
  induction;
  // case Z0
  induction; reflexivity; reflexivity; reflexivity;
  // case Zpos
  assume x; induction;
  reflexivity;
  assume y; simplify; rewrite add_com; reflexivity;
  reflexivity;
  // case Zneg
  assume x; induction;
  reflexivity;
  reflexivity;
  assume y; simplify; rewrite add_com; reflexivity;
end;

// Interaction of succ and doubling functions

symbol pred_double_succ x : π (pred_double (x + 1) = succ_double x) ≔
begin
  induction;
  reflexivity;
  assume x; simplify; rewrite pos_pred_double_succ; reflexivity;
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol succ_pred_double x : π (pred_double x + 1 = double x) ≔
begin
  induction;
  reflexivity;
  assume x; simplify; rewrite succ_pos_pred_double; reflexivity;
  reflexivity;
end;

symbol succ_double_carac x : π (succ_double x = double x + 1) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol double_succ x : π (double (x + 1) = succ_double x + 1) ≔
begin
  induction;
  reflexivity;
  reflexivity;
  induction; reflexivity; reflexivity; reflexivity;
end;

// Negation

symbol - x y ≔ x + ~ y;
notation - infix left 20;

symbol -_same z : π (z + ~ z = 0) ≔
begin
  induction;
  reflexivity;
  simplify; refine sub_same;
  simplify; refine sub_same;
end;

// Associativity

symbol sub_succ x y : π (sub (succ x) y = sub x y + 1) ≔
begin
  induction;
  // case xI
  assume x xrec; induction;
  assume y _; simplify; rewrite xrec; rewrite pred_double_succ;
  rewrite succ_double_carac; reflexivity;
  assume y _; simplify; rewrite xrec; rewrite double_succ; reflexivity;
  simplify; rewrite pos_pred_double_succ; reflexivity;
  // case xO
  assume x xrec; induction;
  assume y _; simplify; rewrite left succ_pred_double; reflexivity;
  assume y _; simplify; rewrite succ_double_carac; reflexivity;
  simplify; rewrite succ_pos_pred_double; reflexivity;
  // case xH
  induction;
  induction; reflexivity; reflexivity; reflexivity;
  induction; reflexivity; reflexivity; reflexivity;
  reflexivity;
end;

symbol add_Zpos_succ x p : π (x + Zpos (succ p) = (x + Zpos p) + 1) ≔
begin
  induction;
  reflexivity;
  assume x p; simplify; rewrite add_succ_right; reflexivity;
  assume x p; simplify; rewrite sub_succ; reflexivity;
end;

symbol sub_add_Zpos a b c : π (sub a b + Zpos c = sub (add a c) b) ≔
begin
  assume a b c;
  refine ind_positive_peano (λ c, sub a b + Zpos c = sub (add a c) b) _ _ c;
  // case xH
  simplify; rewrite sub_succ; reflexivity;
  // case succ
  assume r rrec; rewrite add_Zpos_succ; rewrite rrec;
  rewrite add_succ_right; rewrite sub_succ; reflexivity;
end;

symbol sub_add_Zneg a b c : π (sub a b + Zneg c = sub a (add b c)) ≔
begin
  assume a b c;
  rewrite left sub_opp (add b c) a;
  rewrite left sub_add_Zpos;
  rewrite distr_~_+; rewrite sub_opp; reflexivity;
end;

symbol +_assoc x y z : π (x + y + z = x + (y + z)) ≔
begin
  induction;
  reflexivity;

  assume x; induction; reflexivity;
  assume y; induction; reflexivity;
  // case Zpos - Zpos - Zpos
  assume z; simplify; rewrite add_assoc; reflexivity;
  // case Zpos - Zpos - Zneg
  assume z; simplify; rewrite +_com; rewrite sub_add_Zpos;
  rewrite add_com; reflexivity;

  assume y; induction; reflexivity;
  // case Zpos - Zneg - Zpos
  assume z; simplify; rewrite sub_add_Zpos; rewrite +_com;
  rewrite sub_add_Zpos; rewrite add_com; reflexivity;
  // case Zpos - Zneg - Zneg
  assume z; simplify; rewrite sub_add_Zneg; reflexivity;

  assume x; induction; reflexivity;
  assume y; induction; reflexivity;
  // case Zneg - Zpos - Zpos
  assume z; simplify; rewrite sub_add_Zpos; reflexivity;
  // case Zneg - Zpos - Zneg
  assume z; simplify; rewrite sub_add_Zneg; rewrite +_com;
  rewrite sub_add_Zneg; rewrite add_com; reflexivity;

  assume y; induction; reflexivity;
  // case Zneg - Zneg - Zpos
  assume z; simplify; rewrite +_com; rewrite sub_add_Zneg;
  rewrite add_com; reflexivity;
  // case Zneg - Zneg - Zneg
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

symbol ≐_decides x y : π (x ≐ y = Eq ⇒ x = y) ≔
begin
  induction;
  // case Z0
  induction; reflexivity;
  assume y H; apply ⊥ₑ; refine discr_Lt_Eq H;
  assume y H; apply ⊥ₑ; refine discr_Gt_Eq H;
  // case Zpos
  assume x; induction;
  assume H; apply ⊥ₑ; refine discr_Gt_Eq H;
  assume y H; rewrite compare_decides x y H; reflexivity;
  assume y H; apply ⊥ₑ; refine discr_Gt_Eq H;
  // case Zneg
  assume x; induction;
  assume H; apply ⊥ₑ; refine discr_Lt_Eq H;
  assume y H; apply ⊥ₑ; refine discr_Lt_Eq H;
  assume y H; rewrite compare_decides y x H; reflexivity;
end;

// Commutative properties of ≐

symbol ≐_com x y : π (x ≐ y = revcomp (y ≐ x)) ≔
begin
  induction;
  // case Z0
  induction; reflexivity; reflexivity; reflexivity;
  // case Zpos
  assume x; induction;
  reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
  reflexivity;
  // case Zneg
  assume x; induction;
  reflexivity;
  reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
end;

symbol ≐_opp x y : π (~ x ≐ ~ y = revcomp (x ≐ y)) ≔
begin
  induction;
  // case Z0
  induction; reflexivity; reflexivity; reflexivity;
  // case Zpos
  assume x; induction;
  reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
  reflexivity;
  // case Zneg
  assume x; induction;
  reflexivity;
  reflexivity;
  assume y; simplify; rewrite compare_acc_com; reflexivity;
end;

// General results

symbol simpl_right x a : π (x + a - a = x) ≔
begin
  assume x a; simplify; rewrite +_assoc;
  rewrite -_same; reflexivity;
end;

symbol simpl_inv_right x a : π (x - a + a = x) ≔
begin
  assume x a; simplify; rewrite +_assoc;
  rewrite [~ a + a] +_com; rewrite -_same; reflexivity;
end;

// ≐ with 0

symbol ≐_double x : π ((double x ≐ 0) = (x ≐ 0)) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_pred_double x :
  π (pred_double x ≐ 0 = comparison_case (x ≐ 0) Lt Lt Gt) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_succ_double x :
  π (succ_double x ≐ 0 = comparison_case (x ≐ 0) Gt Lt Gt) ≔
begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_pos_sub x y : π ((sub x y ≐ 0) = compare x y) ≔
begin
  induction;
  // case xI
  assume x xrec; induction;
  assume y _; simplify; rewrite ≐_double; refine xrec y;
  assume y _; simplify; rewrite ≐_succ_double; rewrite xrec;
  rewrite compare_Gt; reflexivity;
  reflexivity;
  // case xO
  assume x xrec; induction;
  assume y _; simplify; rewrite ≐_pred_double; rewrite xrec;
  rewrite compare_Lt; reflexivity;
  assume y _; simplify; rewrite ≐_double; refine xrec y;
  reflexivity;
  // case xH
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol ≐_sub x y : π ((x ≐ y) = (x + ~ y ≐ 0)) ≔
begin
  induction;
  // case Z0
  induction; reflexivity; reflexivity; reflexivity;
  // case Zpos
  assume x; induction;
  reflexivity;
  assume y; simplify; rewrite ≐_pos_sub; reflexivity;
  reflexivity;
  // case Zneg
  assume x; induction;
  reflexivity;
  reflexivity;
  assume y; simplify; rewrite ≐_pos_sub; reflexivity;
end;

// Compatibility of comparison with the addition

symbol ≐_compat_add x y z : π ((x ≐ y) = (x + z ≐ y + z)) ≔
begin
  assume x y z;
  rewrite ≐_sub; rewrite [x in _ = x] ≐_sub;
  simplify; rewrite distr_~_+; rewrite [~ y + ~ z] +_com;
  rewrite +_assoc; rewrite left +_assoc z (~ z) (~ y);
  rewrite -_same z; reflexivity;
end;

// Directional comparison operators

symbol ≤ x y ≔ ¬ (is_Gt (x ≐ y));
notation ≤ infix 10;

symbol < x y ≔ is_Lt (x ≐ y);
notation < infix 10;

symbol ≥ x y ≔ ¬ (x < y);
notation ≤ infix 10;

symbol > x y ≔ ¬ (x ≤ y);
notation > infix 10;

symbol <_≤ x y : π (x < y ⇒ x ≤ y) ≔
begin
  assume x y;
  refine ind_comparison (λ u, is_Lt u ⇒ is_Gt u ⇒ ⊥) _ _ _ (x ≐ y);
  refine (λ x _, x);
  refine (λ _ y, y);
  refine (λ x _, x);
end;

// Compatibility of directional comparison operators

symbol ≤_compat_add x y a : π (x ≤ y ⇒ x + a ≤ y + a) ≔
begin
  assume x y a; simplify;
  assume H; refine fold_implies _; rewrite ≐_sub;
  simplify; refine fold_implies _; rewrite +_assoc;
  rewrite [y + a] +_com; rewrite distr_~_+;
  rewrite left +_assoc a (~ a) (~ y); rewrite -_same;
  rewrite left +_assoc x 0 (~ y); simplify; refine fold_implies _;
  rewrite left ≐_sub x y; refine H;
end;

symbol <_compat_add x y a : π (x < y ⇒ x + a < y + a) ≔
begin
  assume x y a; simplify; assume H; rewrite ≐_sub;
  simplify; rewrite +_assoc; rewrite [y + a] +_com;
  rewrite distr_~_+; rewrite left +_assoc a (~ a) (~ y);
  rewrite -_same; rewrite left +_assoc;
  simplify; rewrite left ≐_sub; refine H;
end;

symbol ≤_compat_≤ x y : π (0 ≤ x ⇒ 0 ≤ y ⇒ 0 ≤ x + y) ≔
begin
  induction;
  assume y _ H; refine H;
  assume x; induction;
  assume _ _; refine λ x, x;
  assume y _ _; refine λ x, x;
  simplify; assume y _ f; apply ⊥ₑ; refine f top;
  assume x; assume y f _; apply ⊥ₑ; refine f top;
end;

symbol <_compat_≤ x y : π (0 < x ⇒ 0 ≤ y ⇒ 0 < x + y) ≔
begin
  induction;
  assume y f _; apply ⊥ₑ; refine f;
  assume x; induction;
  assume _ _; refine top;
  assume y _ _; refine top;
  simplify; assume y _ f; apply ⊥ₑ; refine f top;
  assume x; assume y f _; apply ⊥ₑ; refine f;
end;

// Reflexivity

symbol ≤_refl x : π (x ≤ x) ≔
begin
  assume x; refine ≤_compat_add 0 0 x _; refine (λ x, x);
end;

// Antisymmetry

symbol ≤_antisym x y : π (x ≤ y ⇒ y ≤ x ⇒ x = y) ≔
begin
  assume x y;
  have e : π (¬ (is_Gt (x ≐ y)) ⇒ ¬ (is_Gt (y ≐ x)) ⇒ x = y);
  rewrite ≐_com;
  refine ind_comparison (λ c, (y ≐ x) = c ⇒ ¬ (is_Gt (revcomp c)) ⇒ ¬ (is_Gt c) ⇒ x = y) _ _ _ (y ≐ x) _;
  assume H _ _; symmetry; refine ≐_decides y x H;
  assume _ f _; apply ⊥ₑ; refine f top;
  assume _ _ f; apply ⊥ₑ; refine f top;
  reflexivity; refine e;
end;

// Transitivity theorems

symbol ≤_trans x y z : π (x ≤ y ⇒ y ≤ z ⇒ x ≤ z) ≔
begin
  assume x y z lxy lyz;
  have H : π (0 ≤ (z + ~ y) + (y + ~ x));
  refine ≤_compat_≤ (z - y) (y - x) _ _;
  rewrite left -_same y; refine ≤_compat_add y z (~ y) _; refine lyz;
  rewrite left -_same x; refine ≤_compat_add x y (~ x) _; refine lxy;
  generalize H; refine fold_implies _;
  rewrite +_assoc; rewrite left +_assoc (~ y) y (~ x);
  rewrite [~ y + y] +_com; rewrite -_same;
  rewrite left [in x ≤ z] simpl_inv_right z x;
  refine ≤_compat_add 0 (z - x) x;
end;

symbol <_trans_1 x y z : π (x < y ⇒ y ≤ z ⇒ x < z) ≔
begin
  assume x y z lxy lyz;
  have H : π (0 < (z + ~ y) + (y + ~ x));
  rewrite +_com;
  apply <_compat_≤ (y - x) (z - y); rewrite left -_same x;
  refine <_compat_add x y (~ x) _; refine lxy;
  rewrite left -_same y;
  refine ≤_compat_add y z (~ y) _; refine lyz;
  generalize H; refine fold_implies _;
  rewrite +_assoc; rewrite left +_assoc (~ y) y (~ x);
  rewrite [~ y + y] +_com; rewrite -_same;
  rewrite left [in x < z] simpl_inv_right z x;
  refine <_compat_add 0 (z - x) x;
end;

symbol <_trans_2 x y z : π (x ≤ y ⇒ y < z ⇒ x < z) ≔
begin
  assume x y z lxy lyz;
  have H : π (0 < (z + ~ y) + (y + ~ x));
  apply <_compat_≤ (z - y) (y - x);
  rewrite left -_same y; refine <_compat_add y z (~ y) _; refine lyz;
  rewrite left -_same x; refine ≤_compat_add x y (~ x) _; refine lxy;
  generalize H; refine fold_implies _;
  rewrite +_assoc; rewrite left +_assoc (~ y) y (~ x);
  rewrite [~ y + y] +_com; rewrite -_same;
  rewrite left [in x < z] simpl_inv_right z x;
  refine <_compat_add 0 (z - x) x;
end;

// Multiplication

symbol × : ℤ → ℤ → ℤ;
notation × infix left 22;

rule 0       × _       ↪ 0
with _       × 0       ↪ 0
with Zpos $x × Zpos $y ↪ Zpos (mul $x $y)
with Zpos $x × Zneg $y ↪ Zneg (mul $x $y)
with Zneg $x × Zpos $y ↪ Zneg (mul $x $y)
with Zneg $x × Zneg $y ↪ Zpos (mul $x $y);

// TO BE CONTINUED (theorems about multiplication)
