// Comparison datatype

require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.FOL Blanqui.Lib.Eq;

inductive comparison : TYPE ≔
| Eq : comparison
| Lt : comparison
| Gt : comparison;

// set code for comparison

constant symbol comp : Set;

rule τ comp ↪ comparison;

// Injections in Prop

symbol is_Eq : comparison → Prop;

rule is_Eq Eq ↪ ⊤
with is_Eq Lt ↪ ⊥
with is_Eq Gt ↪ ⊥;

symbol is_Lt : comparison → Prop;

rule is_Lt Eq ↪ ⊥
with is_Lt Lt ↪ ⊤
with is_Lt Gt ↪ ⊥;

symbol is_Gt : comparison → Prop;

rule is_Gt Eq ↪ ⊥
with is_Gt Lt ↪ ⊥
with is_Gt Gt ↪ ⊤;

// Discriminate constructors

symbol discr_Lt_Eq : π (Lt ≠ Eq) ≔
begin
  assume H;
  have f : π (is_Eq Lt)
  { rewrite H; refine top; } ;
  refine ⊥ₑ _ f;
end;

symbol discr_Gt_Eq : π (Gt ≠ Eq) ≔
begin
  assume H;
  have f : π (is_Eq Gt)
  { rewrite H; refine top; } ;
  refine ⊥ₑ _ f;
end;

symbol discr_Gt_Lt : π (Gt ≠ Lt) ≔
begin
  assume H;
  have f : π (is_Lt Gt)
  { rewrite H; refine top; } ;
  refine ⊥ₑ _ f;
end;

// Reverse a comparison

symbol revcomp : comparison → comparison;

rule revcomp Eq ↪ Eq
with revcomp Lt ↪ Gt
with revcomp Gt ↪ Lt;

symbol revcomp_idem c : π (revcomp (revcomp c) = c) ≔
begin
  induction { reflexivity; } { reflexivity; } { reflexivity; }
end;

// Conditional

symbol comparison_case [A] : comparison → τ A → τ A → τ A → τ A;

rule comparison_case Eq $fEq _ _ ↪ $fEq
with comparison_case Lt _ $fLt _ ↪ $fLt
with comparison_case Gt _ _ $fGt ↪ $fGt;
