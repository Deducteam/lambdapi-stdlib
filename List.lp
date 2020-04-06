require open Stdlib.Set Stdlib.Logic Stdlib.Nat

// Type of polymorphic lists

constant symbol list : Set ⇒ Set

definition L a ≔ τ(list a)

set declared "⌑"

constant symbol ⌑ {a} : L a
constant symbol cons {a} : τa ⇒ L a ⇒ L a

set infix 4 "⸬" ≔ cons

// Induction principle on lists

symbol list_ind {a} (p:L a⇒Prop) :
  π(p ⌑) ⇒ (∀x l,π(p l) ⇒ π(p(x⸬l))) ⇒ ∀l,π(p l)

// Length of a list

symbol length {a} : L a ⇒ N

rule length ⌑ → 0
and length (_ ⸬ &l) → succ (length &l)

// Concatenation of two lists

symbol concat {a} : L a ⇒ L a ⇒ L a

set infix right 5 "⋅" ≔ concat
assert a (x y z:L a) ⊢ x⋅y⋅z ≡ x⋅(y⋅z)
assert a x l m ⊢ x⸬l⋅m ≡ x⸬(l⋅m)

rule concat ⌑ &m → &m
and concat (&x⸬&l) &m → &x⸬(concat &l &m)

rule ⌑ ⋅ &m → &m
and (&x ⸬ &l) ⋅ &m → &x ⸬ (&l ⋅ &m)

theorem concat_nil {a} (l:L a) : π(l ⋅ ⌑ = l)
proof
  assume a
  refine list_ind _ _ _
  // case l = ⌑
  reflexivity
  // case l = x ⸬ l'
  assume x l' h
  simpl
  rewrite h
  reflexivity
qed

rule &m ⋅ ⌑ → &m

theorem length_concat {a} (l m : L a) :
  π(length (l ⋅ m) = length l + length m)
proof
  assume a
  refine list_ind _ _ _
  // case l = ⌑
  assume m
  reflexivity
  // case l = x⸬l'
  assume x l' h m
  simpl
  rewrite h
  reflexivity
qed

rule length (&l ⋅ &m) → length &l + length &m

theorem concat_assoc {a} (l m n : L a) : π((l ⋅ m) ⋅ n = l ⋅ (m ⋅ n))
proof
  assume a
  refine list_ind _ _ _
  // case l = ⌑
  assume m n
  reflexivity
  // case l = x⸬l'
  assume x l' h m n
  simpl
  rewrite h
  reflexivity
qed

rule (&l ⋅ &m) ⋅ &n → &l ⋅ (&m ⋅ &n)
