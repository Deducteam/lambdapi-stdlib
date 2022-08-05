// Polymorphic lists

/*
 * Lemmas with incomplete proofs :
 * size_take, rotK, rot_inj, eq_find, filter_undup, count_undup
 * Lemmas using apply ind_𝔹 or ind_B
 * index_size, find_sier, count_size, size_filter, filter_cat, filter_rev, eq_find?, size_undup
 * (ind_B is an induction principle on booleans demonstrated with ind_ind_𝔹, it allow to get hypothesis)
 */

require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.FOL Blanqui.Lib.Eq Blanqui.Lib.Nat Blanqui.Lib.Bool;

// Boolean equality on natural numbers 
symbol ≌ : ℕ → ℕ → 𝔹;

notation ≌ infix 10;

rule 0 ≌ 0 ↪ true
with s $x ≌ s $y ↪ $x ≌ $y
with 0 ≌ s _ ↪ false
with s _ ≌ 0 ↪ false;

// List's definition
(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::

notation ⸬ infix right 4;

// set code for 𝕃

constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;

// Equality on lists
symbol # [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule # $beq □ □ ↪ true
with # $beq $l □ ↪ false
with # $beq □ $l ↪ false
with # $beq ($x ⸬ $lx) ($y ⸬ $ly) ↪ ($beq $x $y) and (# $beq $lx $ly);

// Length of a list
symbol size [a] : 𝕃 a → ℕ;

rule size □ ↪ 0
with size (_ ⸬ $l) ↪ s (size $l);

opaque symbol size0nil [a] (l:𝕃 a) : π (size l = 0) → π (l = □) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h; simplify; assume i; 
    apply ⊥ₑ;
    apply sn≠0 (size l) i; 
  }
end;

// Empty list
symbol is0b : ℕ → 𝔹;
rule is0b 0 ↪ true
with is0b (s $x) ↪ false;

symbol nilp [a] : 𝕃 a → 𝔹 ≔ λ l, is0b (size l);

symbol l : 𝕃 nat ≔ □;
compute nilp (1 ⸬ l);

// Concatenation of two lists

symbol ⋅ [a] : 𝕃 a → 𝕃 a → 𝕃 a;

notation ⋅ infix right 15; // \cdot

assert a (x y z:𝕃 a) ⊢ x ⋅ y ⋅ z ≡ x ⋅ (y ⋅ z);
assert a x l m ⊢ x ⸬ l ⋅ m ≡ x ⸬ (l ⋅ m);

rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m);

opaque symbol cat0s [a] (l:𝕃 a) : π (□ ⋅ l = l) ≔
begin
  reflexivity;
end;

opaque symbol cat1s [a] (x:τ a) (l:𝕃 a) : π ((x ⸬ □) ⋅ l = (x ⸬ l)) ≔
begin
  reflexivity;
end;

opaque symbol cat_cons [a] (x:τ a) (l1:𝕃 a) (l2:𝕃 a) : π ((x ⸬ l1) ⋅ l2 = (x ⸬ l1) ⋅ l2) ≔
begin
  reflexivity;
end;

// Nseq
symbol nseq [a] : ℕ → τ a → 𝕃 a; // nseq n x == a sequence of n x's.

rule nseq 0 $x ↪ □
with nseq (s $n) $x ↪ $x ⸬ (nseq $n $x);

// Ncons
symbol ncons [a] : ℕ → τ a → 𝕃 a → 𝕃 a;  //ncons n x s == a sequence of n x's, followed by s.

rule ncons 0 $x $l ↪ $l
with ncons (s $n) $x $l ↪ $x ⸬ (ncons $n $x $l);

opaque symbol size_ncons [a] n (x:τ a) (l:𝕃 a) : π (size (ncons n x l) = n + size l) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n h x l; simplify; apply feq s (h x l); }
end;

opaque symbol size_nseq [a] n (x:τ a) : π (size (nseq n x) = n) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n h x; simplify; apply feq s (h x); }
end;

opaque symbol cat_nseq [a] n (x:τ a) (l:𝕃 a) : π ((nseq n x) ⋅ l = ncons n x l) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n h x l; simplify; rewrite h x l; reflexivity; }
end;

opaque symbol nseqD [a] n1 n2 (x:τ a) : π (nseq (n1 + n2) x = (nseq n1 x) ⋅ (nseq n2 x)) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n1 h n2 x; simplify; rewrite h n2; reflexivity; }
end;

opaque symbol cats0 [a] (l:𝕃 a) : π(l ⋅ □ = l) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l' h; simplify; rewrite h; reflexivity }
end;

rule $m ⋅ □ ↪ $m;

opaque symbol size_cat [a] (l m : 𝕃 a) : π(size (l ⋅ m) = size l + size m) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l' h m; simplify; rewrite h; reflexivity }
end;

rule size ($l ⋅ $m) ↪ size $l + size $m;

opaque symbol catA  [a] (l m n : 𝕃 a) : π((l ⋅ m) ⋅ n = l ⋅ (m ⋅ n)) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l' h m n; simplify; rewrite h; reflexivity }
end;

rule ($l ⋅ $m) ⋅ $n ↪ $l ⋅ ($m ⋅ $n);

opaque symbol cat_nilp [a] (l1 l2 : 𝕃 a) : π (nilp (l1 ⋅ l2) = (nilp l1 and nilp l2)) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h l2; simplify; reflexivity; }
end;

// List reversal

symbol rev [a] : 𝕃 a → 𝕃 a;

rule rev □ ↪ □
with rev ($x ⸬ $l) ↪ rev $l ⋅ ($x ⸬ □);

opaque symbol rev_concat [a] (l m : 𝕃 a) : π(rev (l ⋅ m) = rev m ⋅ rev l) ≔
begin
  assume a; induction
  { simplify; reflexivity }
  { assume x l h m; simplify; rewrite h; reflexivity }
end;

rule rev ($l ⋅ $m) ↪ rev $m ⋅ rev $l;

opaque symbol rev_idem [a] (l :𝕃 a) : π(rev (rev l) = l) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l h; simplify; rewrite h; reflexivity }
end;

rule rev (rev $l) ↪ $l;

opaque symbol length_rev [a] (l : 𝕃 a) : π(size (rev l) = size l) ≔
begin
  assume a; induction
  { simplify; reflexivity }
  { assume x l h; simplify; rewrite h; reflexivity }
end;

rule size (rev $l) ↪ size $l;

// Rcons
symbol rcons [a] : 𝕃 a → τ a → 𝕃 a;

rule rcons □ $x ↪ $x ⸬ □
with rcons ($e ⸬ $l) $x ↪ $e ⸬ (rcons $l $x);

opaque symbol cats1 [a] (l:𝕃 a) (z:τ a) : π (l ⋅ (z ⸬ □) = rcons l z) ≔
begin
  assume a; 
  induction
  { reflexivity; }
  { assume e l h z; simplify; rewrite h z; reflexivity; }
end;

opaque symbol rcons_cons [a] (x:τ a) (s:𝕃 a) (z:τ a) : π ((rcons (x ⸬ s) z) = (x ⸬ (rcons s z))) ≔
begin
  reflexivity;
end;

// Constructors

symbol seqn_type : ℕ → Set → TYPE;
rule seqn_type 0 $a ↪ 𝕃 $a
with seqn_type (s $n) $a ↪ τ $a → (seqn_type $n $a);

symbol seqn [a] n : seqn_type n a;
symbol seqn' [a] n : 𝕃 a → seqn_type n a;

rule @seqn $a $n ↪ @seqn' $a $n □
with @seqn' $a 0 $l ↪ @rev $a $l
with @seqn' $a (s $n) $l $x ↪ @seqn' $a $n ($x ⸬ $l);

compute seqn 2 1 2;

// is□
symbol is□ [a]: 𝕃 a → 𝔹;

rule is□ □ ↪ true
with is□ ($e ⸬ $l) ↪ false;

compute is□ □;
compute is□ (3 ≤ 5 ⸬ □);

// Head
symbol head [a] : τ a → 𝕃 a → τ a;

rule head $x □ ↪ $x
with head $x ($e ⸬ $l) ↪ $e;

compute head 3 (5 ⸬ 7 ⸬ 6 ⸬ □);
compute head 3 □;

// Behead
symbol behead [a] : 𝕃 a → 𝕃 a;

rule behead □ ↪ □
with behead ($x ⸬ $l) ↪ $l;

compute behead (5 ⸬ 7 ⸬ 6 ⸬ □);

opaque symbol size_behead [a] (l:𝕃 a) : π (size (behead l) = p (size l)) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

// Last λ 
symbol last [a] : τ a → 𝕃 a → τ a;

rule last $x □ ↪ $x
with last $x ($e ⸬ $l) ↪ (last $e $l);

compute last 4 (3 ⸬ 2 ⸬ 1 ⸬ □);
compute last 4 □;

// Belast
symbol belast [a] : τ a → 𝕃 a → 𝕃 a;

rule belast $x □ ↪ □
with belast $x ($e ⸬ $l) ↪ $x ⸬ (belast $e $l);

compute belast 4 (3 ⸬ 2 ⸬ 1 ⸬ □);

// Nth
symbol nth [a] : τ a → 𝕃 a → ℕ → τ a;

rule nth $x0 □ $i ↪ $x0
with nth $x0 ($e ⸬ $l) 0 ↪ $e
with nth $x0 ($e ⸬ $l) (s $n) ↪ (nth $x0 $l $n);

compute nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 0;
compute nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 2;
compute nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 3;
compute nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 42;

// set_nth x0 l i y
symbol set_nth [a] : τ a → 𝕃 a → ℕ → τ a → 𝕃 a;

rule set_nth $x0 □ 0 $y ↪ $y ⸬ □
with set_nth $x0 ($e ⸬ $l) 0 $y ↪ $y ⸬ $l
with set_nth $x0 □ (s $i) $y ↪ $x0 ⸬ (set_nth $x0 □ $i $y)
with set_nth $x0 ($e ⸬ $l) (s $i) $y ↪ $e ⸬ (set_nth $x0 $l $i $y);

compute set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 1 6;
compute set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 2 6;
compute set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 5 6;

// incr_nth l i
symbol incr_nth : 𝕃 nat → τ nat → 𝕃 nat;

rule incr_nth □ 0 ↪ 1 ⸬ □
with incr_nth □ (s $i) ↪ 0 ⸬ (incr_nth □ $i)
with incr_nth ($n ⸬ $l) 0 ↪ (s $n) ⸬ $l
with incr_nth ($n ⸬ $l) (s $i) ↪ $n ⸬ (incr_nth $l $i);

compute incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 1;
compute incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 2;
compute incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 5;

// zip 
// /!\ Drop any extra items
symbol ⊗ : Set → Set → Set;
notation ⊗ infix 10;

symbol ~ [a b] : τ a → τ b → τ (a ⊗ b);
notation ~ infix 10;

symbol zip [a b] : 𝕃 a → 𝕃 b → 𝕃 (a ⊗ b);

rule zip □ □ ↪ □
with zip □ $l ↪ □
with zip $l □ ↪ □
with zip ($e1 ⸬ $l1) ($e2 ⸬ $l2) ↪ ($e1 ~ $e2) ⸬ (zip $l1 $l2);

compute (3 ~ 5) ⸬ (6 ~ 4) ⸬ (7 ~ 2) ⸬ (8 ~ 1) ⸬ □;
 
symbol unzip1 [a b] : 𝕃 (a ⊗ b) → 𝕃 a;
rule @unzip1 $a $b (@□ ($a ⊗ $b)) ↪ (@□ $a)
with @unzip1 $a $b (@⸬ ($a ⊗ $b) (@~ $a $b $e1 $e2) $l) ↪ (@⸬ $a $e1 (@unzip1 $a $b $l));

symbol unzip2 [a b] : 𝕃 (a ⊗ b) → 𝕃 b;
rule @unzip2 $a $b (@□ ($a ⊗ $b)) ↪ (@□ $b)
with @unzip2 $a $b (@⸬ ($a ⊗ $b) (@~ $a $b $e1 $e2) $l) ↪ (@⸬ $b $e2 (@unzip2 $a $b $l));

compute @unzip1 nat nat ((3 ~ 5) ⸬ (6 ~ 4) ⸬ (7 ~ 2) ⸬ (8 ~ 1) ⸬ □);
compute @unzip2 nat nat ((3 ~ 5) ⸬ (6 ~ 4) ⸬ (7 ~ 2) ⸬ (8 ~ 1) ⸬ □);

symbol all2 [a b] : (τ a → τ b → 𝔹) → 𝕃 a → 𝕃 b → 𝔹;

rule all2 $pr □ □ ↪ true
with all2 $pr ($ea ⸬ $la) ($eb ⸬ $lb) ↪ ($pr $ea $eb) and (all2 $pr $la $lb);

/*opaque symbol zip_unzip [a b] (l:𝕃 (a ⊗ b)) : π (@zip a b (@unzip1 a b l) (@unzip2 a b l) = l) ≔
begin
  assume a b l;
  apply @ind_𝕃 (a ⊗ b) (λ ll:𝕃 (a ⊗ b), zip (unzip1 ll) (unzip2 ll) = ll) _ _ l {} {} {} {} {} {} {} {} {} {};
end;*/

opaque symbol unzip1_zip [a b] (la:𝕃 a) (lb:𝕃 b) : π (istrue (size la ≤ size lb)) → π (@unzip1 a b (@zip a b la lb) = la) ≔
begin
  assume a b;
  induction
  { reflexivity; }
  { assume ea la h;
    induction
    { simplify; assume i; apply ⊥ₑ _ i; }
    { assume eb lb i; simplify; assume j; apply feq (λ l:𝕃 a, ea ⸬ l) (h lb j); }
  }
end;

opaque symbol unzip2_zip [a b] (la:𝕃 a) (lb:𝕃 b) : π (istrue (size lb ≤ size la)) → π (@unzip2 a b (@zip a b la lb) = lb) ≔
begin
  assume a b;
  induction
  { simplify; assume lb h; have t:π (size lb = 0) { apply ≤0 (size lb) h; }; symmetry; apply size0nil lb t; }
  { assume ea la h;
    induction
    { reflexivity; }
    { assume eb lb i; simplify; assume j; apply feq (λ l:𝕃 b, eb ⸬ l) (h lb j); }
  }
end;

opaque symbol size1_zip [a b] (la:𝕃 a) (lb:𝕃 b) : π (istrue (size la ≤ size lb)) → π (size (zip la lb) = size la) ≔
begin
  assume a b;
  induction
  { reflexivity; }
  { assume ea la h;
    induction
    { simplify; assume i; apply ⊥ₑ _ i; }
    { assume eb lb i; simplify; assume j; apply feq s (h lb j); }
  }
end;

opaque symbol size2_zip [a b] (la:𝕃 a) (lb:𝕃 b) : π (istrue (size lb ≤ size la)) → π (size (zip la lb) = size lb) ≔
begin
  assume a b;
  induction
  { assume lb; simplify; assume h; symmetry; apply ≤0 (size lb) h; }
  { assume ea la h; 
    induction
    { reflexivity; }
    { assume eb lb i; simplify; assume j; apply feq s (h lb j); }
  }
end;

opaque symbol size_zip [a b] (la:𝕃 a) (lb:𝕃 b) : π (size (zip la lb) = min (size la) (size lb)) ≔
begin
  assume a b;
  induction
  { reflexivity }
  { assume ea la h;
    induction
    { reflexivity; }
    { assume eb lb i; simplify; apply feq s (h lb); }
  }
end;

//Double induction
opaque symbol seq_ind2 [a b] (P:𝕃 a → 𝕃 b → Prop) : π (P □ □) → (Π la:𝕃 a, Π lb:𝕃 b, Π ea:τ a, Π eb:τ b, π (size la = size lb) → π (P la lb) → π (P (ea ⸬ la) (eb ⸬ lb))) → Π la:𝕃 a, Π lb:𝕃 b, π (size la = size lb) → π (P la lb) ≔
begin
  assume a b P P0 PH;
  induction
  { induction
    { assume h; apply P0; }
    { assume eb lb; simplify; assume h1 h2; have t:π (⊥) { apply sn≠0 (size lb); symmetry; apply h2; }; apply ⊥ₑ _ t; }
  }
  { assume ea la h;
    induction
    { simplify; assume i; apply ⊥ₑ _ (sn≠0 (size la) i);}
    { assume eb lb i; simplify; assume j; have t:π (size la = size lb) { apply s_inj j; }; apply PH la lb ea eb t (h lb t); }
  }
end;

opaque symbol zip_cat [a b] (la sa:𝕃 a) (lb sb:𝕃 b) : π (size la = size lb) → π (zip (la ⋅ sa) (lb ⋅ sb) = (zip la lb) ⋅ (zip sa sb)) ≔
begin
  assume a b la sa lb sb h;
  apply @seq_ind2 a b (λ l1:𝕃 a, λ l2:𝕃 b, (zip (l1 ⋅ sa) (l2 ⋅ sb) = (zip l1 l2) ⋅ (zip sa sb))) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 h1 h2; simplify; apply feq (λ l:𝕃 (a ⊗ b), (e1 ~ e2) ⸬ l) h2; 
  };
end;

opaque symbol nth_zip [a b] (x:τ a) (y:τ b) (la:𝕃 a) (lb:𝕃 b) i: π (size la = size lb) → π (nth (x ~ y) (zip la lb) i = ((nth x la i) ~ (nth y lb i))) ≔
begin
  assume a b x y;
  induction
  { simplify; assume lb i h; have t: π (lb = □) { apply size0nil lb; symmetry; apply h; }; rewrite t; reflexivity; }
  { assume ea la h;
    induction
    { simplify; assume i j; apply ⊥ₑ _ (sn≠0 (size la) j); }
    { assume eb lb k;
      induction
      { simplify; assume m; reflexivity; }
      { simplify; assume i m n; apply h lb i _; apply s_inj n; }
    }
  }
end;

opaque symbol rev_zip [a b] (la:𝕃 a) (lb:𝕃 b) : π (size la = size lb) → π (rev (zip la lb) = zip (rev la) (rev lb)) ≔
begin
  assume a b la lb h;
  apply seq_ind2 (λ l1:𝕃 a, λ l2:𝕃 b, rev (zip l1 l2) = zip (rev l1) (rev l2)) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 i j; simplify; rewrite zip_cat (rev l1) (e1 ⸬ □) (rev l2) (e2 ⸬ □) i; simplify; rewrite left j; reflexivity;
  };
end;

// Drop
symbol drop [a] : ℕ → 𝕃 a → 𝕃 a;

rule drop 0 $l ↪ $l
with drop $n □ ↪ □
with drop (s $n) ($x ⸬ $l) ↪ drop $n $l;

compute drop 3 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □);
compute drop 10 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □);

opaque symbol drop0 [a] (l:𝕃 a) : π (drop 0 l = l) ≔
begin
  reflexivity;
end;

opaque symbol drop_oversize [a] n (l:𝕃 a) : π (istrue (size l ≤ n)) → π (drop n l = □) ≔
begin
  assume a;
  induction
  { assume l h; 
    have t:π (size l = 0) { apply ≤0 (size l) h;};
    simplify; apply size0nil l t;
  }
  {
    assume n h;
    induction
    { reflexivity; }
    { assume e l i; simplify; refine h l; }
  }
end;

opaque symbol drop_size [a] (l:𝕃 a) : π (drop (size l) l = □) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h; simplify; apply h; }
end;

rule drop (size l) l ↪ □;

opaque symbol drop_cons [a] (e:τ a) (l:𝕃 a) : Π n0, π (drop (s n0) (e ⸬ l) = drop n0 l) ≔
begin
  assume a e l n0; reflexivity;
end;

opaque symbol size_drop [a] (l:𝕃 a) : Π n0, π (size (drop n0 l) = size l - n0) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h; simplify; 
    induction
    { reflexivity; }
    { assume n0 i; simplify; apply h n0; } 
  }
end;

opaque symbol size_cons [a] (e:τ a) n (l:𝕃 a): π (size l = n ⇔ size (e ⸬ l) = s n) ≔
begin
  assume a e n l;
  apply ∧ᵢ {
    generalize n; induction
    { assume l h; simplify; rewrite h; reflexivity; }
    { assume n h l i; simplify; apply feq s i;}
  } {
    generalize n; induction
    { assume l; simplify; assume i; apply s_inj i;}
    { assume n; simplify; assume h l i; apply s_inj i; }
  };
end;

opaque symbol drop_size_cat [a] n0 (l1:𝕃 a) (l2:𝕃 a) : π (size l1 = n0) → π (drop n0 (l1 ⋅ l2) = l2) ≔
begin
  assume a;
  induction
  { assume l1 l2 h; simplify; have t:π (l1 = □) {apply size0nil l1 h;}; rewrite t; reflexivity; }
  { assume n0 h; 
    induction
    { assume l2; simplify; assume i; apply ⊥ₑ; apply sn≠0 n0; symmetry; apply i; }
    { assume e l1 i l2; simplify; assume j; apply h l1 l2; apply s_inj j; }
  }
end;

opaque symbol drop_drop [a] (l:𝕃 a) n1 n2 : π (drop n1 (drop n2 l) = drop (n1 + n2) l) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h n1;
    induction
    { reflexivity; }
    { assume n2 i; simplify; apply h n1 n2; }
  }
end;

// Take
symbol take [a] : ℕ → 𝕃 a → 𝕃 a;

rule take 0 $l ↪ □
with take $n □ ↪ □
with take (s $n) ($x ⸬ $l) ↪ $x ⸬ (take $n $l);

compute take 3 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □);
compute take 10 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □);

opaque symbol take0 [a] (l: 𝕃 a) : π (take 0 l = □) ≔
begin
  reflexivity;
end;

opaque symbol take_cons [a] n (x:τ a) (l:𝕃 a) : π (take (s n) (x ⸬ l) = (x ⸬ take n l)) ≔
begin
  assume a l; reflexivity;
end;

opaque symbol take_size [a] (l: 𝕃 a) : π (take (size l) l = l) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h; simplify; rewrite h; reflexivity; }
end;

opaque symbol take_oversize [a] n (l:𝕃 a) : π (istrue (size l ≤ n)) → π (take n l = l) ≔
begin
  assume a;
  induction
  { assume l h; simplify; symmetry; apply size0nil l; apply ≤0 (size l) h; }
  { assume n h; 
    induction
    { reflexivity; }
    { assume e l i; simplify; assume j; rewrite h l j; reflexivity; }
  }
end;

opaque symbol cat_take_drop [a] n (l:𝕃 a) : π (take n l ⋅ drop n l = l) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n h;
    induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; }
  }
end;

opaque symbol size_takel [a] n (l:𝕃 a) : π (istrue (n ≤ size l)) → π (size (take n l) = n) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n h;
    induction
    { simplify; assume i; apply ⊥ₑ _ i; }
    { assume e l i; simplify; assume j; apply feq s; apply h l j; }
  }
end;

//Récupérer l'hypothèse
opaque symbol size_take [a] n (l:𝕃 a) : π (size (take n l) = if (n < size l) n (size l)) ≔
begin
  assume a n l;
  refine ind_B (λ b:𝔹, (size (take n l) = (if b n (size l)))) (n < size l) _ _ {
    assume h; rewrite h; simplify;
  } {
    //assume h; rewrite h; simplify;
  };
abort;

opaque symbol size_take_min [a] (n:ℕ) (l:𝕃 a) : π (size (take n l) = min n (size l)) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n h;
    induction
    { reflexivity; }
    { assume e l i; simplify; apply feq s (h l); }
  }
end;

opaque symbol take_size_cat [a] n (l1 l2:𝕃 a) : π (size l1 = n) → π (take n (l1 ⋅ l2) = l1) ≔
begin
  assume a;
  induction
  { assume l1 l2 h; simplify; symmetry; apply size0nil l1 h; }
  { assume n h; 
    induction
    { assume l2; simplify; assume i; apply ⊥ₑ; apply sn≠0 n _; symmetry; apply i; }
    { assume e1 l1 i l2 j; simplify; apply feq (λ l:𝕃 a, (e1 ⸬ l)); apply h l1 l2; 
      apply ⇔ₑ₂ (size l1 = n) (size (e1 ⸬ l1) = s n) (size_cons e1 n l1) j; 
    }
  }
end;

opaque symbol takel_cat [a] (l1 l2:𝕃 a) : Π n, π (istrue (n ≤ size l1)) → π (take n (l1 ⋅ l2) = take n l1) ≔
begin
  assume a;
  induction
  { assume l2 n h; have t:π (n = 0) { apply ≤0 n h; }; rewrite t; reflexivity; }
  { assume e1 l1 h l2;
    induction
    { reflexivity; }
    { assume n i; simplify; assume j; apply feq (λ l:𝕃 a, e1 ⸬ l); apply h l2 n j; }
  }
end;

opaque symbol take_drop [a] m n (l:𝕃 a): π (take m (drop n l) = drop n (take (m + n) l)) ≔
begin
  assume a;
  induction
  { induction
    { reflexivity; }
    { assume m h;
      induction
      { reflexivity; }
      { assume e l i; simplify; rewrite left .[m in take m l] add0n m; rewrite left h l; reflexivity; }
    }
  }
  { assume n h;
    induction
    { reflexivity; }
    { assume m i; 
      induction
      { reflexivity; }
      { assume e l j; simplify; apply i l; }
    }
  }
end;

opaque symbol takeD [a] m n (l:𝕃 a) : π (take (m + n) l = take m l ⋅ take n (drop m l)) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume m h;
    induction
    { reflexivity; }
    { assume n i;
      induction
      { reflexivity; }
      { assume e l j; simplify; apply feq (λ l:𝕃 a, e ⸬ l); rewrite left addnS; apply h (s n) l; }
    }
  }
end;

opaque symbol takeC [a] (l:𝕃 a) i j: π (take i (take j l) = take j (take i l)) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume e l h;
    induction
    { reflexivity; }
    { assume i h2;
      induction
      { reflexivity; }
      { assume j h3; simplify; rewrite h i j; reflexivity; }
    }
  }
end;

// Rot
symbol rot [a] : ℕ → 𝕃 a → 𝕃 a ≔ λ n, λ l, ((drop n l) ⋅ (take n l));

compute rot 2 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □);

opaque symbol π_rot [a] n (l:𝕃 a) : π (drop n l ⋅ take n l = rot n l) ≔
begin
  reflexivity;
end;

opaque symbol rot0 [a] (l:𝕃 a) : π (rot 0 l = l) ≔
begin
  reflexivity;
end;

opaque symbol size_rot [a] (l:𝕃 a) : Π n0, π (size (rot n0 l) = size l) ≔
begin
  assume a l n0; simplify; rewrite addnC; rewrite left @size_cat a (take n0 l) (drop n0 l);
  rewrite cat_take_drop n0 l; reflexivity; 
end;

opaque symbol rot_oversize [a] n (l:𝕃 a) : π (istrue (size l ≤ n)) → π (rot n l = l) ≔
begin
  assume a n l h; simplify; rewrite drop_oversize n l h; rewrite take_oversize n l h; reflexivity;
end;

opaque symbol rot_size [a] (l:𝕃 a) : π (rot (size l) l = l) ≔
begin
  assume a l; simplify; rewrite drop_size l; rewrite take_size l; reflexivity;
end;

opaque symbol rot_size_cat [a] (l1 l2:𝕃 a) : π (rot (size l1) (l1 ⋅ l2) = l2 ⋅ l1) ≔
begin
  assume a l1 l2; simplify; 
  rewrite drop_size_cat (size l1) l1 l2 (eq_refl (size l1));
  rewrite take_size_cat (size l1) l1 l2 (eq_refl (size l1));
  reflexivity;
end;

opaque symbol take_take [a] n m : π (istrue (n ≤ m)) → π (`∀ l:𝕃 a, take n (take m l) = take n l) ≔
begin
  assume a;
  induction
  { reflexivity; }
  { assume n; simplify; assume h;
    induction
    { simplify; assume i; apply ⊥ₑ _ i; }
    { assume m i; simplify; assume j;
      induction
      { reflexivity; }
      { assume e l k; simplify; apply feq (λ l:𝕃 a, e ⸬ l) (h m j l); }
    }
  }
end;

// Rotr
symbol rotr [a] : ℕ → 𝕃 a → 𝕃 a ≔ λ n, λ l, rot (size l - n) l;

compute rotr 2 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □);

opaque symbol π_rotr [a] n (l:𝕃 a) : π (drop (size l - n) l ⋅ take (size l - n) l = rotr n l) ≔
begin
  reflexivity;
end;

opaque symbol rotr0 [a] (l:𝕃 a) : π (rotr 0 l = l) ≔
begin
  assume a l; simplify; rewrite drop_size l; rewrite take_size l; reflexivity;
end;

opaque symbol rotK [a] n (l:𝕃 a) : π (rot n (rotr n l) = l) ≔
begin
abort;

opaque symbol rot_inj [a] : Π (n0:ℕ), Π (l1:𝕃 a), Π (l2:𝕃 a), π (rot n0 l1 = rot n0 l2) → π (l1 = l2) ≔
begin
  assume a;
  induction
  { assume l1 l2 h; rewrite left rot0 l1; rewrite left rot0 l2; apply h; }
  { assume n0 h l1 l2 i; apply h l1 l2; }
abort;

// Inl
symbol inl [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → 𝔹;

rule inl $beq $x □ ↪ false
with inl $beq $x ($y ⸬ $l) ↪ ($beq $x $y) or (inl $beq $x $l);

compute inl (≌) 2 (3 ⸬ 2 ⸬ 1 ⸬ □);
compute inl (≌) 4 (3 ⸬ 2 ⸬ 1 ⸬ □);

opaque symbol in_cons [a] (beq:τ a → τ a → 𝔹) x y (l:𝕃 a) : π ((inl beq x (y ⸬ l)) = ((beq x y) or (inl beq x l))) ≔
begin
  assume a beq x y;
  induction
  { reflexivity; }
  { assume e l h; simplify; reflexivity; }
end;

opaque symbol in_nil [a] (beq:τ a → τ a → 𝔹) x : π (inl beq x □ = false) ≔
begin
  assume a beq x; reflexivity;
end;

opaque symbol mem_seq1 [a] (beq:τ a → τ a → 𝔹) x y : π (inl beq x (y ⸬ □) = (beq x y)) ≔
begin
  assume a beq x y; reflexivity;
end;

opaque symbol mem_cat [a] (beq:τ a → τ a → 𝔹) x (l1:𝕃 a) (l2:𝕃 a) : π ((inl beq x (l1 ⋅ l2)) = ((inl beq x l1) or (inl beq x l2))) ≔
begin
  assume a beq x;
  induction
  { reflexivity; }
  { assume e1 l1 h; simplify; assume l2; rewrite h l2; rewrite orA; reflexivity; }
end;

opaque symbol mem_head [a] (beq:τ a → τ a → 𝔹) x (l:𝕃 a) : π (beq x x = true) → π (istrue (inl beq x (x ⸬ l))) ≔
begin
  assume a beq x l hrefl; simplify; rewrite hrefl; apply top;
end;

//Lemma mem_last x s : last x s \in x :: s.

opaque symbol mem_take [a] (beq:τ a → τ a → 𝔹) n (l:𝕃 a) x : π (istrue (inl beq x (take n l))) → π (istrue (inl beq x l)) ≔
begin
  assume a beq n l x h;
  rewrite left cat_take_drop n l;
  rewrite mem_cat beq x (take n l) (drop n l);
  refine or_i1 (inl beq x (take n l)) (inl beq x (drop n l)) h;
end;

opaque symbol mem_drop [a] (beq:τ a → τ a → 𝔹) n (l:𝕃 a) x : π (istrue (inl beq x (drop n l))) → π (istrue (inl beq x l)) ≔
begin
  assume a beq n l x h;
  rewrite left cat_take_drop n l;
  rewrite mem_cat beq x (take n l) (drop n l);
  refine or_i2 (inl beq x (take n l)) (inl beq x (drop n l)) h;
end;

//index
symbol index [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → ℕ;
symbol index_c [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → ℕ → ℕ;

rule index $beq $x □ ↪ 0
with index $beq $x ($y ⸬ $l) ↪ if ($beq $x $y) 0 (s (index $beq $x $l));

compute index (≌) 2 (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □);
compute index (≌) 26 (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □);

opaque symbol index_size [a] (beq:τ a → τ a → 𝔹) (x:τ a) (l:𝕃 a) : π (istrue (index beq x l ≤ size l)) ≔
begin
  assume a beq x;
  induction
  { simplify; apply top; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ b:𝔹, istrue (if b 0 (s (index beq x l)) ≤ s (size l))) _ _ (beq x e) {
      simplify; apply top;
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol index_head [a] (beq:τ a → τ a → 𝔹) (x:τ a) (l:𝕃 a) : π (beq x x = true) → π (index beq x (x ⸬ l) = 0) ≔
begin
  assume a beq x l hrefl; simplify; rewrite hrefl; reflexivity;
end;

// Has
symbol has [a] : (τ a → 𝔹) → 𝕃 a → 𝔹;

rule has $p □ ↪ false
with has $p ($x ⸬ $l) ↪ if ($p $x) true (has $p $l);

symbol prt: ℕ → 𝔹 ≔ λ x, (x + 1 ≌ 3);

compute has prt (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □);
compute has prt (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □);

// All
symbol all [a] : (τ a → 𝔹) → 𝕃 a → 𝔹;

rule all $p □ ↪ true // Attention à ce cas de la définition
with all $p ($x ⸬ $l) ↪ if ($p $x) (all $p $l) false;

compute all prt (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □);
compute all prt (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □);

// Find
symbol find [a] : (τ a → 𝔹) → 𝕃 a → ℕ;

rule find $p □ ↪ 0
with find $p ($x ⸬ $l) ↪ if ($p $x) 0 (s (find $p $l));

compute find prt (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □);
compute find prt (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □);

opaque symbol find_size [a] (pr:τ a → 𝔹) (l:𝕃 a) : π (istrue (find pr l ≤ size l)) ≔
begin
  assume a pr;
  induction
  { simplify; apply top; }
  { assume e l; simplify; assume h;
    refine ind_𝔹 (λ x:𝔹, istrue (if x 0 (s (find pr l)) ≤ s (size l))) _ _ (pr e) {
      simplify; apply top;
    } {
      simplify; apply h;
    };
  }
end;

// Count
symbol count [a] : (τ a → 𝔹) → 𝕃 a → ℕ;

rule count $p □ ↪ 0
with count $p ($x ⸬ $l) ↪ if ($p $x) (s (count $p $l)) (count $p $l);

compute count prt (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □);
compute count prt (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □);

opaque symbol count_size [a] (pr:τ a → 𝔹) (l:𝕃 a) : π (istrue (count pr l ≤ size l)) ≔
begin
  assume a pr;
  induction
  { simplify; apply top; }
  { assume e l h; simplify; 
    refine ind_𝔹 (λ x:𝔹, istrue (if x (s (count pr l)) (count pr l) ≤ s (size l))) _ _ (pr e) {
      simplify; apply h;
    } {
      simplify; refine leq_trans (count pr l) (size l) (s (size l)) h (leqnSn (size l)); 
    };
  }
end;

// Count_mem
symbol count_mem [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → ℕ;

rule count_mem $beq $e $l ↪ count ($beq $e) $l;

compute count_mem (≌) 2 (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □);
compute count_mem (≌) 2 (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □); 

// Constant
symbol is_constant [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝔹;

rule is_constant $beq □ ↪ true
with is_constant $beq ($x ⸬ $l) ↪ if (all ($beq $x) $l) true false;

compute is_constant (≌) (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □);
compute is_constant (≌) □;
compute is_constant (≌) (2 ⸬ 2 ⸬ 2 ⸬ 1 ⸬ □);

// Uniq
symbol uniq [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝔹;

rule uniq $beq □ ↪ true
with uniq $beq ($x ⸬ $l) ↪ if (not (inl $beq $x $l)) (uniq $beq $l) false;

compute uniq (≌) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □);
compute uniq (≌) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □);

// Subseq
symbol subseq [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule subseq $beq □ □ ↪ true
with subseq $beq □ ($x ⸬ $l) ↪ false
with subseq $beq ($x ⸬ $l) □ ↪ false
with subseq $beq ($x ⸬ $l1) ($y ⸬ $l2) ↪ if ($beq $x $y) (subseq $beq $l1 $l2) false;

compute subseq (≌) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □);
compute subseq (≌) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □);

// Prefix
symbol is_prefix [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule is_prefix $beq □ _ ↪ true
with is_prefix $beq ($x ⸬ $l1) □ ↪ false
with is_prefix $beq ($x ⸬ $l1) ($y ⸬ $l2) ↪ if ($beq $x $y) (is_prefix $beq $l1 $l2) false;

compute is_prefix (≌) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □);

// Suffix
symbol is_suffix [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule is_suffix $beq $l1 $l2 ↪ is_prefix $beq (rev $l1) (rev $l2);

compute is_suffix (≌) (4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □);

// Infix
symbol is_infix [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule is_infix $beq □ _ ↪ true
with is_infix $beq ($x ⸬ $l1) □ ↪ false
with is_infix $beq ($x ⸬ $l1) ($y ⸬ $l2) ↪ if ($beq $x $y) (is_prefix $beq $l1 $l2) (is_infix $beq ($x ⸬ $l1) $l2);

compute is_infix (≌) (51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □);

// Infix_index
symbol infix_index [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → ℕ;

rule infix_index $beq □ _ ↪ 0
with infix_index $beq ($x ⸬ $l1) □ ↪ 0
with infix_index $beq ($x ⸬ $l1) ($y ⸬ $l2) ↪ if ($beq $x $y) (if (is_prefix $beq $l1 $l2) 0 (s (size $l2))) (s (infix_index $beq ($x ⸬ $l1) $l2));
//(s (size $l2)) because $x :: $l2 

compute infix_index (≌) (51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □);
compute infix_index (≌) (51 ⸬ 4 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □);

// Perm_eq
symbol perm_eq [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule perm_eq $beq $l1 $l2 ↪ all (λ x, (count_mem $beq x $l1 ≌ count_mem $beq x $l2)) ($l1 ⋅ $l2);

compute perm_eq (≌) (59 ⸬ 58 ⸬ 4 ⸬ 2 ⸬ □) (58 ⸬ 4 ⸬ 2 ⸬ 59 ⸬ □);
compute perm_eq (≌) (59 ⸬ 58 ⸬ 4 ⸬ 2 ⸬ □) (58 ⸬ 4 ⸬ 2 ⸬ 69 ⸬ □);

//Filter
symbol filter [a] : (τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule filter $p □ ↪ □
with filter $p ($x ⸬ $l) ↪ if ($p $x) ($x ⸬ (filter $p $l)) (filter $p $l);

compute filter prt (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ 2 ⸬ 68 ⸬ □);

symbol rmfilter [a] : (τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule rmfilter $p □ ↪ □
with rmfilter $p ($x ⸬ $l) ↪ if ($p $x) (filter $p $l) ($x ⸬ (filter $p $l));

opaque symbol size_filter [a] (pr:τ a → 𝔹) (l:𝕃 a) : π (size (filter pr l) = count pr l) ≔
begin
  assume a pr;
  induction
  { reflexivity; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ x:𝔹, size (if x (e ⸬ filter pr l) (filter pr l)) = (if x (s (count pr l)) (count pr l))) _ _ (pr e) {
      simplify; apply feq s h;
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol filter_cat [a] (pr:τ a → 𝔹) (l1 l2:𝕃 a) : π (filter pr (l1 ⋅ l2) = (filter pr l1) ⋅ (filter pr l2)) ≔
begin
  assume a pr;
  induction
  { reflexivity; }
  { assume e1 l1 h l2; simplify;
    refine ind_𝔹 (λ x:𝔹, (if x (e1 ⸬ filter pr (l1 ⋅ l2)) (filter pr (l1 ⋅ l2))) = (if x (e1 ⸬ filter pr l1) (filter pr l1) ⋅ filter pr l2)) _ _ (pr e1) {
      simplify; rewrite h l2; reflexivity;
    } {
      simplify; rewrite h l2; reflexivity;
    }
  }
end;

opaque symbol filter_rev [a] (pr:τ a → 𝔹) (l:𝕃 a) : π (filter pr (rev l) = rev (filter pr l)) ≔
begin
  assume a pr;
  induction
  { reflexivity; }
  { assume e l h; simplify; rewrite filter_cat pr (rev l) (e ⸬ □); simplify;
    refine ind_𝔹 (λ b:𝔹, (filter pr (rev l) ⋅ (if b (e ⸬ □) □) = rev (if b (e ⸬ filter pr l) (filter pr l)))) _ _ (pr e) {
      simplify; rewrite h; reflexivity;
    } {
      simplify; rewrite h; reflexivity;
    };
  }
end;

opaque symbol count_cat [a] (pr:τ a → 𝔹) (l1 l2:𝕃 a) : π (count pr (l1 ⋅ l2) = count pr l1 + count pr l2) ≔
begin
  assume a pr l1 l2; rewrite left size_filter pr l1; rewrite left size_filter pr l2; rewrite left size_filter pr (l1 ⋅ l2);
  rewrite filter_cat pr l1 l2; rewrite left size_cat (filter pr l1) (filter pr l2); reflexivity;
end;

//Some lemmas on lists's equality
opaque symbol eq_find [a] (beq:τ a → τ a → 𝔹) (pr:τ a → 𝔹) (l1:𝕃 a) (l2:𝕃 a): π (istrue (# beq l1 l2)) → π (istrue ((find pr l1) ≌ (find pr l2))) ≔
begin
  assume a beq pr;
  induction
  { simplify; assume l2 h; apply ⊥ₑ _ h; }
  { assume e1 l1 h;
    induction
    { simplify; assume i; apply ⊥ₑ _ i; }
    { assume e2 l2 i; simplify; assume j; 
      type ind_B;
      apply ind_B (λ b:𝔹, istrue (if b 0 (s (find pr l1)) ≌ if (pr e2) 0 (s (find pr l2)))) (pr e1) _ _ {
        assume k; rewrite k; simplify;
        apply ind_B (λ b:𝔹, istrue (0 ≌ if b 0 (s (find pr l2)))) (pr e2) _ _ {
          assume m; rewrite m; simplify; apply top;
        } {
          assume m; rewrite m; simplify;

        }
      } {

      };
      /*apply ind_𝔹 (λ b:𝔹, istrue (if b 0 (s (find pr l1)) ≌ if (pr e2) 0 (s (find pr l2)))) _ _ (pr e1) {
        simplify; 
        apply ind_𝔹 (λ b:𝔹, istrue (0 ≌ if b 0 (s (find pr l2)))) _ _ (pr e2) {
          simplify; apply top;
        } {
          simplify; //rewrite beq e1 e2 = false
        };
      } {
        simplify;
        apply ind_𝔹 (λ b:𝔹, istrue (s (find pr l1) ≌ if b 0 (s (find pr l2)))) _ _ (pr e2) {
          simplify;
        } {
          simplify; apply h l2; apply and_el2 (beq e1 e2) (# beq l1 l2) j;
        }
      };*/
    }
  }
abort;

//Undup
symbol undup [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule undup $beq □ ↪ □
with undup $beq ($x ⸬ $l) ↪ if (inl $beq $x (undup $beq $l)) (undup $beq $l) ($x ⸬ (undup $beq $l));

compute undup (≌) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ 2 ⸬ 3 ⸬ □);

opaque symbol size_undup [a] (beq:τ a → τ a → 𝔹) (l:𝕃 a) : π (istrue (size (undup beq l) ≤ size l)) ≔
begin
  assume a beq;
  induction
  { simplify; apply top; }
  { assume e l h; simplify; 
    refine ind_𝔹 (λ x:𝔹, istrue (size (if x (undup beq l) (e ⸬ (undup beq l))) ≤ s (size l))) _ _ (inl beq e (undup beq l)) {
      simplify;
      refine leq_trans (size (undup beq l)) (size l) (s (size l)) h (leqnSn (size l));
    } {
      simplify; apply h;
    }; 
  }
end;

opaque symbol undup_uniq [a] (beq:τ a → τ a → 𝔹) (l:𝕃 a) : π (istrue (uniq beq (undup beq l))) ≔
begin
  assume a beq;
  induction
  { simplify; apply top; }
  { assume e l h; simplify;
    refine ind_B (λ b:𝔹, (istrue(uniq beq (if b (undup beq l) (e ⸬ (undup beq l)))))) (inl beq e (undup beq l)) _ _ {
      assume i; rewrite i; simplify; apply h;
    } {
      assume i; rewrite i; simplify; rewrite i; simplify; apply h; 
    }; 
  }
end;

opaque symbol filter_undup [a] (beq:τ a → τ a → 𝔹) (pr:τ a → 𝔹) (l:𝕃 a) : π (filter pr (undup beq l) = undup beq (filter pr l)) ≔
begin
  assume a beq pr;
abort;

opaque symbol count_undup [a] (beq:τ a → τ a → 𝔹) (pr:τ a → 𝔹) (l:𝕃 a) : π (istrue (count pr (undup beq l) ≤ count pr l)) ≔
begin
  assume a beq pr l;
  rewrite left size_filter pr l;
  rewrite left size_filter pr (undup beq l);
abort;

//Map
symbol map [a b] : (τ a → τ b) → 𝕃 a → 𝕃 b;

rule map $f □ ↪ □
with map $f ($x ⸬ $l) ↪ ($f $x) ⸬ (map $f $l);

symbol ft : τ nat → 𝔹;
rule ft $x ↪ boolification (istrue (3 ≤ $x));

compute map (ft) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □);

opaque symbol map_cons [a b] (f:τ a → τ b) (l:𝕃 a) : Π x:τ a, π ((map f (x ⸬ l)) = ((f x) ⸬ (map f l))) ≔
begin
  assume a b f l x; reflexivity;
end;

opaque symbol map_cat [a b] (f:τ a → τ b) (l1:𝕃 a) (l2:𝕃 a) : π (map f (l1 ⋅ l2) = map f l1 ⋅ map f l2) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume e1 l1 h l2; simplify; rewrite h l2; reflexivity; }
end;

opaque symbol size_map [a b] (f:τ a → τ b) (l:𝕃 a) : π (size (map f l) = size l) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume e l h; simplify; apply feq s h; }
end;

opaque symbol behead_map [a b] (f:τ a → τ b) (l:𝕃 a): π (behead (map f l) = map f (behead l)) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

opaque symbol map_rcons [a b] (f:τ a → τ b) (l:𝕃 a) (e:τ a) : π (map f (rcons l e) = rcons (map f l) (f e)) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume x l h e; simplify; rewrite h e; reflexivity; }
end;

opaque symbol last_map [a b] (f:τ a → τ b) (l:𝕃 a) (x:τ a) : π (last (f x) (map f l) = f (last x l)) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume e l h x; simplify; rewrite h e; reflexivity; }
end;

opaque symbol belast_map [a b] (f:τ a → τ b) (l:𝕃 a) (x:τ a) : π (belast (f x) (map f l) = map f (belast x l)) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume e l h x; simplify; rewrite h e; reflexivity; }
end;

opaque symbol map_take [a b] (f:τ a → τ b) n (l:𝕃 a) : π (map f (take n l) = take n (map f l)) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume n h;
    induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; } 
  }
end;

opaque symbol map_drop [a b] (f:τ a → τ b) n (l:𝕃 a) : π (map f (drop n l) = drop n (map f l)) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume n h;
    induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; } 
  }
end;

opaque symbol map_rot [a b] (f:τ a → τ b) n (l:𝕃 a) : π (map f (rot n l) = rot n (map f l)) ≔
begin
  assume a b f n l; simplify; rewrite map_cat f (drop n l) (take n l);
  rewrite map_take f n l; rewrite map_drop f n l; reflexivity; 
end;

opaque symbol map_rotr [a b] (f:τ a → τ b) n (l:𝕃 a) : π (map f (rotr n l) = rotr n (map f l)) ≔
begin
  assume a b f n l; simplify; rewrite map_cat f (drop (size l - n) l) (take (size l - n) l);
  rewrite map_drop f (size l - n) l; rewrite map_take f (size l - n) l;
  rewrite size_map f l; reflexivity;
end;

opaque symbol map_rev [a b] (f:τ a → τ b) (l:𝕃 a) : π (map f (rev l) = rev (map f l)) ≔
begin
  assume a b f;
  induction
  { reflexivity; }
  { assume e l h; simplify; rewrite map_cat f (rev l) (e ⸬ □); rewrite h; simplify; reflexivity; }
end;

symbol aay [a] (e:τ a) (l:𝕃 a): π ((e ⸬ l) = □) → π (⊥);
symbol aai [a] (e1 e2:τ a) (l1 l2:𝕃 a): π ((e1 ⸬ l1) = (e2 ⸬ l2) ⇔ (e1 = e2) ∧ (l1 = l2));

opaque symbol inj_map [a b] (f:τ a → τ b) : π (`∀ x, `∀ y, f x = f y ⇒ x = y) → Π l1:𝕃 a, Π l2:𝕃 a, π (map f l1 = map f l2) → π (l1 = l2) ≔
begin
  assume a b f h;
  induction
  { induction
    { reflexivity; }
    { assume e l i; simplify; assume j; apply ⊥ₑ; 
      have t:π (⊥) { apply aay (f e) (map f l); symmetry; apply j; }; apply t;
    }
  }
  { assume e1 l1 i;
    induction
    { simplify; assume j; apply ⊥ₑ;
      have t:π (⊥) { apply aay (f e1) (map f l1) j; }; apply t;
    }
    {
      assume e2 l2 j; simplify; assume k;
      have t:π (f e1 = f e2 ∧ map f l1 = map f l2) {
        apply ⇔ₑ₁ ((f e1 ⸬ map f l1) = (f e2 ⸬ map f l2)) (f e1 = f e2 ∧ map f l1 = map f l2) (aai (f e1) (f e2) (map f l1) (map f l2)) k;
      };
      have t1: π (f e1 = f e2) { apply ∧ₑ₁ (f e1 = f e2) (map f l1 = map f l2) t; };
      have t2: π (map f l1 = map f l2) { apply ∧ₑ₂ (f e1 = f e2) (map f l1 = map f l2) t; };
      apply ⇔ₑ₂ ((e1 ⸬ l1) = (e2 ⸬ l2)) (e1 = e2 ∧ l1 = l2) (aai e1 e2 l1 l2);
      apply ∧ᵢ (e1 = e2) (l1 = l2) {
        apply h e1 e2 t1;
      } {
        apply i l2 t2;
      };
    }
  }
end;

// sumn
symbol sumn : 𝕃 nat → ℕ;

rule sumn □ ↪ 0
with sumn ($x ⸬ $l) ↪ $x + sumn $l;

compute sumn (3 ⸬ 2 ⸬ 1 ⸬ □);

// prodn
symbol prodn : 𝕃 nat → ℕ;

rule prodn □ ↪ 1
with prodn ($x ⸬ $l) ↪ $x × (prodn $l);

compute prodn (3 ⸬ 2 ⸬ 1 ⸬ □);