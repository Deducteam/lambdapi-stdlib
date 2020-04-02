require open Set Logic Nat

// Type of polymorphic lists

constant symbol list : Set ⇒ Set

definition L a ≔ S (list a)

constant symbol nil {a} : L a
constant symbol cons {a} : S a ⇒ L a ⇒ L a

// Induction principle on lists

symbol list_ind {a} p :
  P(p nil) ⇒ (∀(x:S a),∀l,P(p l)⇒P(p(cons x l))) ⇒ ∀l,P(p l)

// Length of a list

symbol length {a} : L a ⇒ N

rule length nil → 0
//and length (cons _ &l) → length &l // not accepted FIXME
and length (@cons &a _ &l) → succ (@length &a &l)

// Concatenation of two lists

symbol concat {a} : L a ⇒ L a ⇒ L a

set infix 5 "++" ≔ concat

rule nil ++ &m → &m
//and cons &x &l ++ &m → cons &x (&l ++ &m) // not accepted FIXME
and concat (@cons &a &x &l) &m → @cons &a &x (@concat &a &l &m)

theorem concat_nilr {a} (l:L a) : P (l ++ nil = l)
proof
  assume a
  refine list_ind _ _ _
  // case l = nil
  reflexivity
  // case l = cons x l'
  assume x l' h
  simpl
  rewrite h
  reflexivity
qed

rule &m ++ nil → &m

theorem length_concat {a} (l m : L a) :
  P (length (l ++ m) = length l + length m)
proof
  assume a
  refine list_ind _ _ _
  // case l = nil
  assume m
  reflexivity
  // case l = cons x l'
  assume x l' h m
  simpl
  rewrite h
  reflexivity
qed

rule @length &a (&l ++ &m) → @length &a &l + @length &a &m

theorem concat_assoc {a} (l m n : L a) : P((l ++ m) ++ n = l ++ (m ++ n))
proof
  assume a
  refine list_ind _ _ _
  // case l = nil
  assume m n
  reflexivity
  // case l = cons x l'
  assume x l' h m n
  simpl
  rewrite h
  reflexivity
qed

//rule (&l ++ &m) ++ &n → &l ++ (&m ++ &n)
rule @concat &a (&l ++ &m) &n → @concat &a &l (@concat &a &m &n)
