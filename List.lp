require open Stdlib.Set Stdlib.Logic Stdlib.Nat Stdlib.Bool;

// Type of polymorphic lists

constant symbol list : Set → Set;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a
| cons : τ a → 𝕃 a → 𝕃 a;

set infix 4 "⸬" ≔ cons; // :: 

rule 𝕃 $a ↪ τ (list $a);

// Length of a list

symbol length {a} : 𝕃 a → ℕ;

rule length □ ↪ 0
with length (_ ⸬ $l) ↪ suc (length $l);

// Concatenation of two lists

symbol concat {a} : 𝕃 a → 𝕃 a → 𝕃 a;

set infix right 5 "⋅" ≔ concat; // \cdot

assert a (x y z:𝕃 a) ⊢ x ⋅ y ⋅ z ≡ x ⋅ (y ⋅ z);
assert a x l m ⊢ x ⸬ l ⋅ m ≡ x ⸬ (l ⋅ m);

rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m);

opaque symbol concat_nil {a} (l:𝕃 a) : π(l ⋅ □ = l) ≔
begin
  assume a;
  refine ind_𝕃 _ _ _ _;
  // case l = □
  reflexivity;
  // case l = x ⸬ l'
  assume x l' h;
  simpl;
  rewrite h;
  reflexivity;
end;

rule $m ⋅ □ ↪ $m;

opaque symbol length_concat {a} (l m : 𝕃 a) :
  π(length (l ⋅ m) = length l + length m) ≔
begin
  assume a;
  refine ind_𝕃 _ _ _ _;
  // case l = □
  assume m;
  reflexivity;
  // case l = x⸬l'
  assume x l' h m;
  simpl;
  rewrite h;
  reflexivity;
end;

rule length ($l ⋅ $m) ↪ length $l + length $m;

opaque symbol concat_assoc {a} (l m n : 𝕃 a) : π((l ⋅ m) ⋅ n = l ⋅ (m ⋅ n)) ≔
begin
  assume a;
  refine ind_𝕃 _ _ _ _;
  // case l = □
  assume m n;
  reflexivity;
  // case l = x⸬l'
  assume x l' h m n;
  simpl;
  rewrite h;
  reflexivity;
end;

rule ($l ⋅ $m) ⋅ $n ↪ $l ⋅ ($m ⋅ $n);
