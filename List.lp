require open Stdlib.Set Stdlib.Logic Stdlib.Nat

// Type of polymorphic lists

constant symbol list : Set → Set

set declared "𝕃"

definition 𝕃a ≔ τ (list a)

set declared "□"

constant symbol □ {a} : 𝕃a
constant symbol cons {a} : τa → 𝕃a → 𝕃a

set infix 4 "⸬" ≔ cons

// Induction principle on lists

symbol list_ind {a} (p:𝕃a→Prop) :
  π(p □) → (Πx l,π(p l) → π(p(x⸬l))) → Πl,π(p l)

// Length of a list

symbol length {a} : 𝕃a → ℕ

rule length □ ↪ 0
with length (_ ⸬ $l) ↪ suc (length $l)

// Concatenation of two lists

symbol concat {a} : 𝕃a → 𝕃a → 𝕃a

set infix right 5 "⋅" ≔ concat

assert a (x y z:𝕃a) ⊢ x⋅y⋅z ≡ x⋅(y⋅z)
assert a x l m ⊢ x⸬l⋅m ≡ x⸬(l⋅m)

rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m)

theorem concat_nil {a} (l:𝕃a) : π(l ⋅ □ = l)
proof
  assume a
  refine list_ind _ _ _
  // case l = □
  reflexivity
  // case l = x ⸬ l'
  assume x l' h
  simpl
  rewrite h
  reflexivity
qed

rule $m ⋅ □ ↪ $m

theorem length_concat {a} (l m : 𝕃a) :
  π(length (l ⋅ m) = length l + length m)
proof
  assume a
  refine list_ind _ _ _
  // case l = □
  assume m
  reflexivity
  // case l = x⸬l'
  assume x l' h m
  simpl
  rewrite h
  reflexivity
qed

rule length ($l ⋅ $m) ↪ length $l + length $m

theorem concat_assoc {a} (l m n : 𝕃a) : π((l ⋅ m) ⋅ n = l ⋅ (m ⋅ n))
proof
  assume a
  refine list_ind _ _ _
  // case l = □
  assume m n
  reflexivity
  // case l = x⸬l'
  assume x l' h m n
  simpl
  rewrite h
  reflexivity
qed

rule ($l ⋅ $m) ⋅ $n ↪ $l ⋅ ($m ⋅ $n)
