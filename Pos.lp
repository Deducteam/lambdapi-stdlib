// Positive binary integers

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq;

inductive positive : TYPE ≔
| xI : positive → positive
| xO : positive → positive
| xH : positive;

// set code for positive

constant symbol pos : Set;

rule τ pos ↪ positive;

// Injections in Prop

symbol is_xI : positive → Prop;

rule is_xI (xI _) ↪ ⊤
with is_xI (xO _) ↪ ⊥
with is_xI xH     ↪ ⊥;

symbol is_xO : positive → Prop;

rule is_xO (xI _) ↪ ⊥
with is_xO (xO _) ↪ ⊤
with is_xO xH     ↪ ⊥;

symbol is_xH : positive → Prop;

rule is_xH (xI _) ↪ ⊥
with is_xH (xO _) ↪ ⊥
with is_xH xH     ↪ ⊤;

// Discriminate constructors

symbol discr_xI_xH p : π (xI p ≠ xH)
≔ begin
  assume p H;
  have f : π (is_xI xH);
  rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

symbol discr_xO_xH p : π (xO p ≠ xH)
≔ begin
  assume p H;
  have f : π (is_xO xH);
  rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

symbol discr_xI_xO p q : π (xI p ≠ xO q)
≔ begin
  assume p q H;
  have f : π (is_xI (xO q));
  rewrite left H; refine top;
  refine ⊥ₑ _ f;
end;

// Successor function

symbol succ : positive → positive;

rule succ (xI $p) ↪ xO (succ $p)
with succ (xO $p) ↪ xI $p
with succ xH ↪ xO xH;

// Nat-like Induction Principle

symbol ind_positive_peano Q :
  π (Q xH) →
  (Π p, π (Q p) → π (Q (succ p))) →
  Π p, π (Q p);
// ≔ begin
//   assume Q qH qS p;
//   have Gi : Π p P, π (P xH) → (Π x, π (P x) → π (P (succ x))) → π (P p);
//   induction;
// end;
// Can't prove this yet because the predicate on which we want to do the
// induction is :
// λ p, `Π P, P xH ⇒ (`∀ x, P x ⇒ P (succ x)) ⇒ P p
// We need `Π, that is: a deep symbol for the universal quantification on Prop

// Addition of positive numbers with and without a carry

symbol add : positive → positive → positive;
symbol add_carry : positive → positive → positive;

rule add (xI $p) (xI $q) ↪ xO (add_carry $p $q)
with add (xI $p) (xO $q) ↪ xI (add $p $q)
with add (xO $p) (xI $q) ↪ xI (add $p $q)
with add (xO $p) (xO $q) ↪ xO (add $p $q)
with add $x      xH      ↪ succ $x
with add xH      $y      ↪ succ $y;

rule add_carry (xI $p) (xI $q) ↪ xI (add_carry $p $q)
with add_carry (xI $p) (xO $q) ↪ xO (add_carry $p $q)
with add_carry (xO $p) (xI $q) ↪ xO (add_carry $p $q)
with add_carry (xO $p) (xO $q) ↪ xI (add $p $q)
with add_carry $x      xH      ↪ add $x (xO xH) // not succ (succ x)
with add_carry xH      $y      ↪ add (xO xH) $y; // for efficiency reasons


// Check that 7 + 5 = 12
// assert ⊢ add (xI (xI xH)) (xI (xO xH)) ≡ xO (xO (xI xH));
// Check that 110101010 + 101101100 ≡ 1100010110 in base 2 (426 + 364 ≡ 790)
// assert ⊢ add (xO (xI (xO (xI (xO (xI (xO (xI xH)))))))) (xO (xO (xI (xI (xO (xI (xI (xO xH)))))))) ≡ (xO (xI (xI (xO (xI (xO (xO (xO (xI xH)))))))));

symbol succ_add x y : π (succ (add x y) = add_carry x y)
≔ begin
  induction;
  assume p prec;
  induction;
  reflexivity;
  assume q _; simplify; rewrite prec; reflexivity;
  reflexivity;

  assume p prec;
  induction;
  assume q _; simplify; rewrite prec; reflexivity;
  reflexivity;
  reflexivity;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol add_succ x y : π (add (succ x) y = succ (add x y))
≔ begin
  induction;
  assume p prec;
  induction;
  assume q _; simplify; rewrite prec; rewrite succ_add; reflexivity;
  assume q _; simplify; rewrite prec; reflexivity;
  reflexivity;

  assume p prec;
  induction;
  assume q _; simplify; rewrite succ_add; reflexivity;
  reflexivity;
  reflexivity;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol add_assoc x y z : π (add (add x y) z = add x (add y z))
≔ begin
  refine ind_positive_peano (λ x, `∀ y, `∀ z, add (add x y) z = add x (add y z)) _ _;
  refine add_succ;

  assume x xrec y z;
  rewrite add_succ;
  rewrite add_succ;
  rewrite add_succ;
  rewrite xrec;
  reflexivity;
end;

symbol add_succ_right x y : π (add x (succ y) = succ (add x y))
≔ begin
  refine ind_positive_peano (λ x, `∀ y, add x (succ y) = succ (add x y)) _ _;
  reflexivity;
  assume x xrec y;
  rewrite add_succ; rewrite add_succ; rewrite xrec;
  reflexivity;
end;

symbol add_com x y : π (add x y = add y x)
≔ begin
  refine ind_positive_peano (λ x, `∀ y, add x y = add y x) _ _;
  reflexivity;
  assume x xrec y;
  rewrite add_succ; rewrite add_succ_right; rewrite xrec;
  reflexivity;
end;

