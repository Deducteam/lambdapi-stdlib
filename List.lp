/* Library on polymorphic lists

following https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/seq.v

by Quentin Buzet (July 2022)

(lemmas with unfinished proofs:
size_take, rotK, rot_inj, eq_find, filter_undup, count_undup). */

require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.FOL Blanqui.Lib.Eq
  Blanqui.Lib.Nat Blanqui.Lib.Bool;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::

notation ⸬ infix right 20;

// set code for 𝕃

constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;

// is□

symbol is□ [a]: 𝕃 a → 𝔹;

rule is□ □ ↪ true
with is□ (_ ⸬ _) ↪ false;

// non confusion of constructors

opaque symbol ⸬≠□ [a] [x:τ a] [l] : π (x ⸬ l ≠ □) ≔
begin
  assume a x l h; refine ind_eq h (λ l, istrue(is□ l)) top
end;

opaque symbol □≠⸬ [a] [x:τ a] [l] : π (□ ≠ x ⸬ l) ≔
begin
  assume a x l h; /*FIXME:apply ⸬≠□ fails*/ refine @⸬≠□ a x l _;
  symmetry; apply h
end;

// head

symbol head [a] : τ a → 𝕃 a → τ a;

rule head $x □ ↪ $x
with head _ ($x ⸬ _) ↪ $x;

// tail

symbol behead [a] : 𝕃 a → 𝕃 a;

rule behead □ ↪ □
with behead (_ ⸬ $l) ↪ $l;

// injectivity of constructors

opaque symbol ⸬_inj [a] [x:τ a] [l y m] : π(x ⸬ l = y ⸬ m) → π(x = y ∧ l = m) ≔
begin
  assume a x l y m e; apply ∧ᵢ { apply feq (head x) e } { apply feq behead e }
end;

// boolean equality on lists

symbol eql [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule eql _ □ □ ↪ true
with eql _ (_ ⸬ _) □ ↪ false
with eql _ □ (_ ⸬ _) ↪ false
with eql $beq ($x ⸬ $l) ($y ⸬ $m) ↪ ($beq $x $y) and (eql $beq $l $m);

opaque symbol eql_correct a beq: π(`∀ x:τ a, `∀ y, istrue(beq x y) ⇒ x = y) →
  π(`∀ l, `∀ m, istrue(eql beq l m) ⇒ l = m) ≔
begin
  assume a beq beq_correct; induction
  { induction
    { reflexivity }
    { simplify; assume y m i c; refine ⊥ₑ c }
  }
  { assume x l h; induction
    { simplify; assume c; refine ⊥ₑ c; }
    { simplify; assume y m i c;
      //FIXME: apply feq2 (⸬) fails
      refine feq2 (⸬) _ _
      { apply beq_correct; //FIXME: apply andₑ₁ c fails
        apply @andₑ₁ (beq x y) (eql beq l m) c}
      { apply h; //FIXME: apply andₑ₂ c fails
        refine @andₑ₂ (beq x y) (eql beq l m) c
      } 
    }
  }
end;

opaque symbol eql_complete a beq: π(`∀ x:τ a, `∀ y, x = y ⇒ istrue(beq x y)) →
  π(`∀ l, `∀ m, l = m ⇒ istrue(eql beq l m)) ≔
begin
  simplify; //FIXME: remove
  assume a beq beq_complete; induction
  { assume m i; rewrite left i; apply top; }
  { simplify /*FIXME*/; assume x l h; induction
    { assume j; apply ⸬≠□ j; }
    { assume y m i j; simplify;
      have j': π(x = y ∧ l = m) { apply ⸬_inj j };
      apply @istrue_and (beq x y) (eql beq l m) /*FIXME*/; apply ∧ᵢ
      { apply beq_complete x y; apply ∧ₑ₁ j' }
      { //FIXME: apply h fails
        refine h m _; apply ∧ₑ₂ j' }
    }
  }
end;

// size

symbol size [a] : 𝕃 a → ℕ;

rule size □ ↪ 0
with size (_ ⸬ $l) ↪ s (size $l);

opaque symbol size0nil [a] (l:𝕃 a) : π (size l = 0) → π (l = □) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h i; apply ⊥ₑ; apply s≠0 i; }
end;

symbol nilp [a] l ≔ is0 (@size a l);

opaque symbol size_behead [a] (l:𝕃 a) : π (size (behead l) = p (size l)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

// concatenation

symbol ⋅ [a] : 𝕃 a → 𝕃 a → 𝕃 a; notation ⋅ infix right 30; // \cdot

assert x y z ⊢ x ⋅ y ⋅ z ≡ x ⋅ (y ⋅ z);
assert x l m ⊢ x ⸬ l ⋅ m ≡ x ⸬ (l ⋅ m);

rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m);

opaque symbol cat0s [a] (l:𝕃 a) : π (□ ⋅ l = l) ≔
begin
  reflexivity;
end;

opaque symbol cat1s [a] (x:τ a) l : π ((x ⸬ □) ⋅ l = (x ⸬ l)) ≔
begin
  reflexivity;
end;

opaque symbol cat_cons [a] (x:τ a) l1 l2 : π ((x ⸬ l1) ⋅ l2 = x ⸬ (l1 ⋅ l2)) ≔
begin
  reflexivity;
end;

// nseq

symbol nseq [a] : ℕ → τ a → 𝕃 a;

rule nseq 0 _ ↪ □
with nseq (s $n) $x ↪ $x ⸬ (nseq $n $x);

// ncons

symbol ncons [a] : ℕ → τ a → 𝕃 a → 𝕃 a;

rule ncons 0 _ $l ↪ $l
with ncons (s $n) $x $l ↪ $x ⸬ ncons $n $x $l;

opaque symbol size_ncons [a] n (x:τ a) l : π (size (ncons n x l) = n + size l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x l; simplify; apply feq s (h x l); }
end;

opaque symbol size_nseq [a] n (x:τ a) : π (size (nseq n x) = n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x; simplify; apply feq s (h x); }
end;

opaque symbol cat_nseq [a] n (x:τ a) l : π (nseq n x ⋅ l = ncons n x l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x l; simplify; rewrite h x l; reflexivity; }
end;

opaque symbol nseqD [a] n1 n2 (x:τ a) :
  π (nseq (n1 + n2) x = nseq n1 x ⋅ nseq n2 x) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n1 h n2 x; simplify; rewrite h n2; reflexivity; }
end;

opaque symbol cats0 [a] (l:𝕃 a) : π(l ⋅ □ = l) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x ⸬ l'
    { assume x l' h; simplify; rewrite h; reflexivity; }
end;

rule $m ⋅ □ ↪ $m;

opaque symbol size_cat [a] (l m : 𝕃 a) : π(size (l ⋅ m) = size l + size m) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x⸬l'
    { assume x l' h m; simplify; rewrite h; reflexivity; }
end;

rule size ($l ⋅ $m) ↪ size $l + size $m;

opaque symbol catA  [a] (l m n : 𝕃 a) : π((l ⋅ m) ⋅ n = l ⋅ (m ⋅ n)) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x⸬l'
    { assume x l' h m n; simplify; rewrite h; reflexivity; }
end;

rule ($l ⋅ $m) ⋅ $n ↪ $l ⋅ ($m ⋅ $n);

opaque symbol cat_nilp [a] (l1 l2 : 𝕃 a) :
  π (nilp (l1 ⋅ l2) = (nilp l1 and nilp l2)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h l2; simplify; reflexivity; }
end;

// list reversal

symbol rev [a] : 𝕃 a → 𝕃 a;

rule rev □ ↪ □
with rev ($x ⸬ $l) ↪ rev $l ⋅ ($x ⸬ □);

opaque symbol rev_concat [a] (l m : 𝕃 a) : π(rev (l ⋅ m) = rev m ⋅ rev l) ≔
begin
  assume a;
  induction
    // case l = □
    { simplify; reflexivity; }
    // case l = ⸬
    { assume x l h m; simplify; rewrite h; reflexivity; }
end;

rule rev ($l ⋅ $m) ↪ rev $m ⋅ rev $l;

opaque symbol rev_idem [a] (l :𝕃 a) : π(rev (rev l) = l) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l h;
    /*FIXME: if no rule rev_concat, rewrite rev_concat fails:
      Uncaught [File "src/handle/rewrite.ml", line 166
    rewrite @rev_concat a;*/
    simplify; rewrite h; reflexivity }
end;

//rule rev (rev $l) ↪ $l; creates confluence problems

opaque symbol size_rev [a] (l : 𝕃 a) : π(size (rev l) = size l) ≔
begin
  assume a;
  induction
    // case l = □
    { simplify; reflexivity; }
    // case l = ⸬
    { assume x l h; simplify; rewrite h; reflexivity; }
end;

//rule size (rev $l) ↪ size $l; // confluence modulo C

// rcons

symbol rcons [a] : 𝕃 a → τ a → 𝕃 a;

rule rcons □ $x ↪ $x ⸬ □
with rcons ($e ⸬ $l) $x ↪ $e ⸬ (rcons $l $x);

opaque symbol cats1 [a] (l:𝕃 a) (z:τ a) : π (l ⋅ (z ⸬ □) = rcons l z) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h z; simplify; rewrite h z; reflexivity; }
end;

opaque symbol rcons_cons [a] (x:τ a) (s:𝕃 a) (z:τ a) :
  π (rcons (x ⸬ s) z = x ⸬ rcons s z) ≔
begin
  reflexivity;
end;

// seqn

symbol Seqn : ℕ → Set → TYPE;

rule Seqn 0 $a ↪ 𝕃 $a
with Seqn (s $n) $a ↪ τ $a → Seqn $n $a;

symbol seqn' [a] n : 𝕃 a → Seqn n a;

rule seqn' 0 $l ↪ rev $l
with seqn' (s $n) $l $x ↪ seqn' $n ($x ⸬ $l);

symbol seqn [a] n ≔ @seqn' a n □;

assert ⊢ seqn 2 1 2 ≡ 1 ⸬ 2 ⸬ □;

// last

symbol last [a] : τ a → 𝕃 a → τ a;

rule last $x □ ↪ $x
with last _ ($e ⸬ $l) ↪ last $e $l;

assert ⊢ last 4 (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 1;
assert ⊢ last 4 □ ≡ 4;

// belast

symbol belast [a] : τ a → 𝕃 a → 𝕃 a;

rule belast _ □ ↪ □
with belast $x ($e ⸬ $l) ↪ $x ⸬ belast $e $l;

assert ⊢ belast 4 (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 4 ⸬ 3 ⸬ 2 ⸬ □;

// nth

symbol nth [a] : τ a → 𝕃 a → ℕ → τ a;

rule nth $x □ _ ↪ $x
with nth _ ($e ⸬ _) 0 ↪ $e
with nth $x (_ ⸬ $l) (s $n) ↪ nth $x $l $n;

assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 0 ≡ 3;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 2 ≡ 1;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 3 ≡ 4;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 42 ≡ 4;

// set_nth

symbol set_nth [a] : τ a → 𝕃 a → ℕ → τ a → 𝕃 a;

rule set_nth _ □ 0 $y ↪ $y ⸬ □
with set_nth _ (_ ⸬ $l) 0 $y ↪ $y ⸬ $l
with set_nth $x □ (s $i) $y ↪ $x ⸬ set_nth $x □ $i $y
with set_nth $x ($e ⸬ $l) (s $i) $y ↪ $e ⸬ set_nth $x $l $i $y;

assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 1 6 ≡ 3 ⸬ 6 ⸬ 1 ⸬ □;
assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 2 6 ≡ 3 ⸬ 2 ⸬ 6 ⸬ □;
assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 5 6 ≡ 3 ⸬ 2 ⸬ 1 ⸬ 42 ⸬ 42 ⸬ 6 ⸬ □;

// incr_nth

symbol incr_nth : 𝕃 nat → τ nat → 𝕃 nat;

rule incr_nth □ 0 ↪ 1 ⸬ □
with incr_nth □ (s $i) ↪ 0 ⸬ (incr_nth □ $i)
with incr_nth ($n ⸬ $l) 0 ↪ (s $n) ⸬ $l
with incr_nth ($n ⸬ $l) (s $i) ↪ $n ⸬ (incr_nth $l $i);

assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 1 ≡ 3 ⸬ 3 ⸬ 1 ⸬ □;
assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 2 ≡ 3 ⸬ 2 ⸬ 2 ⸬ □;
assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 5 ≡ 3 ⸬ 2 ⸬ 1 ⸬ 0 ⸬ 0 ⸬ 1 ⸬ □;

// zip 

symbol zip [a b] : 𝕃 a → 𝕃 b → 𝕃 (a × b);

rule zip □ □ ↪ □
with zip □ _ ↪ □
with zip _ □ ↪ □
with zip ($x ⸬ $l) ($y ⸬ $m) ↪ $x & $y ⸬ zip $l $m;

symbol unzip1 [a b] : 𝕃 (a × b) → 𝕃 a;

rule unzip1 □  ↪ □
with unzip1 ($x & _ ⸬ $l) ↪ $x ⸬ unzip1 $l;

symbol unzip2 [a b] : 𝕃 (a × b) → 𝕃 b;

rule unzip2 □ ↪ □
with unzip2 (_ & $y ⸬ $l) ↪ $y ⸬ unzip2 $l;

assert ⊢ unzip1 ((3 & 5) ⸬ (6 & 4) ⸬ (7 & 2) ⸬ (8 & 1) ⸬ □) ≡ 3 ⸬ 6 ⸬ 7 ⸬ 8 ⸬ □;
assert ⊢ unzip2 ((3 & 5) ⸬ (6 & 4) ⸬ (7 & 2) ⸬ (8 & 1) ⸬ □) ≡ 5 ⸬ 4 ⸬ 2 ⸬ 1 ⸬ □;

symbol all2 [a b] : (τ a → τ b → 𝔹) → 𝕃 a → 𝕃 b → 𝔹;

rule all2 _ □ □ ↪ true
with all2 $p ($x ⸬ $l) ($y ⸬ $m) ↪ ($p $x $y) and (all2 $p $l $m);

opaque symbol unzip1_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (istrue (size la ≤ size lb)) → π (unzip1 (zip la lb) = la) ≔
begin
  assume a b; induction
  { reflexivity; }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ i; }
    { assume eb lb i j; apply feq (λ l, ea ⸬ l) (h lb j); }
  }
end;

opaque symbol unzip2_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (istrue (size lb ≤ size la)) → π (unzip2 (zip la lb) = lb) ≔
begin
  assume a b; induction
  { assume lb h;
     have t:π (size lb = 0) { apply ≤0 (size lb) h; };
     symmetry; apply size0nil lb t; }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i j; apply feq (λ l, eb ⸬ l) (h lb j); }
  }
end;

opaque symbol size1_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (istrue (size la ≤ size lb)) → π (size (zip la lb) = size la) ≔
begin
  assume a b; induction
  { reflexivity; }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ i; }
    { assume eb lb i j; apply feq s (h lb j); }
  }
end;

opaque symbol size2_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (istrue (size lb ≤ size la)) → π (size (zip la lb) = size lb) ≔
begin
  assume a b; induction
  { assume lb h; symmetry; apply ≤0 (size lb) h; }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i j; apply feq s (h lb j); }
  }
end;

opaque symbol size_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size (zip la lb) = min (size la) (size lb)) ≔
begin
  assume a b; induction
  { reflexivity }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i; simplify; apply feq s (h lb); }
  }
end;

// double induction

opaque symbol seq_ind2 [a b] (p:𝕃 a → 𝕃 b → Prop) :
  π (p □ □) →
  (Π la lb ea eb, π(size la = size lb) → π(p la lb) → π(p (ea ⸬ la) (eb ⸬ lb)))
  → Π la lb, π(size la = size lb) → π(p la lb) ≔
begin
  assume a b p p0 pH; induction
  { induction
    { assume h; apply p0; }
    { assume eb lb h1 h2; apply ⊥ₑ; apply s≠0 [size lb]; symmetry; apply h2 }
  }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ (s≠0 i); }
    { assume eb lb i j;
      have t:π (size la = size lb) { apply s_inj j; };
      apply pH la lb ea eb t (h lb t); }
  }
end;

opaque symbol zip_cat [a b] (la sa:𝕃 a) (lb sb:𝕃 b) :
  π (size la = size lb) → π (zip (la ⋅ sa) (lb ⋅ sb) = zip la lb ⋅ zip sa sb) ≔
begin
  assume a b la sa lb sb h;
  apply @seq_ind2 a b (λ l1 l2, (zip (l1 ⋅ sa) (l2 ⋅ sb) = zip l1 l2 ⋅ zip sa sb)) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 h1 h2; simplify; apply feq (λ l, e1 & e2 ⸬ l) h2; 
  };
end;

opaque symbol nth_zip [a b] (x:τ a) (y:τ b) la lb i: π(size la = size lb) →
  π(nth (x & y) (zip la lb) i = nth x la i & nth y lb i) ≔
begin
  assume a b x y; induction
  { assume lb i h;
    have t: π (lb = □) { apply size0nil lb; symmetry; apply h; };
    rewrite t; reflexivity; }
  { assume ea la h; induction
    { assume i j; apply ⊥ₑ (s≠0 j); }
    { assume eb lb k; induction
      { assume m; reflexivity; }
      { assume i m n; apply h lb i _; apply s_inj n; }
    }
  }
end;

opaque symbol rev_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size la = size lb) → π (rev (zip la lb) = zip (rev la) (rev lb)) ≔
begin
  assume a b la lb h;
  apply seq_ind2 (λ l1 l2, rev (zip l1 l2) = zip (rev l1) (rev l2)) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 i j; simplify;
    have i': π(size(rev l1) = size(rev l2))
      { rewrite @size_rev; rewrite @size_rev; apply i}; 
    rewrite zip_cat (rev l1) (e1 ⸬ □) (rev l2) (e2 ⸬ □) i';
    rewrite left j; reflexivity;
  };
end;

// drop

symbol drop [a] : ℕ → 𝕃 a → 𝕃 a;

rule drop 0 $l ↪ $l
with drop _ □ ↪ □
with drop (s $n) (_ ⸬ $l) ↪ drop $n $l;

assert ⊢ drop 3 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 1 ⸬ 41 ⸬ □;
assert ⊢ drop 10 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ □;

opaque symbol drop0 [a] (l:𝕃 a) : π (drop 0 l = l) ≔
begin
  reflexivity;
end;

opaque symbol drop_oversize [a] n (l:𝕃 a) :
  π (istrue (size l ≤ n)) → π (drop n l = □) ≔
begin
  assume a; induction
  { assume l h; 
    have t:π (size l = 0) { apply ≤0 (size l) h;};
    simplify; apply size0nil l t;
  }
  {
    assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; refine h l; }
  }
end;

opaque symbol drop_size [a] (l:𝕃 a) : π (drop (size l) l = □) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; simplify; apply h; }
end;

//rule drop (size $l) $l ↪ □;

opaque symbol drop_cons [a] (e:τ a) l n : π (drop (s n) (e ⸬ l) = drop n l) ≔
begin
  assume a e l n; reflexivity;
end;

opaque symbol size_drop [a] (l:𝕃 a) n : π (size (drop n l) = size l - n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; simplify; induction
    { reflexivity; }
    { assume n i; simplify; apply h n; } 
  }
end;

opaque symbol size_cons [a] (e:τ a) n l : π (size l = n ⇔ size (e ⸬ l) = s n) ≔
begin
  assume a e n l; apply ∧ᵢ {
    generalize n; induction
    { assume l h; simplify; rewrite h; reflexivity; }
    { assume n h l i; simplify; apply feq s i;}
  } {
    generalize n; induction
    { assume l i; apply s_inj i;}
    { assume n h l i; apply s_inj i; }
  };
end;

opaque symbol drop_size_cat [a] n (l1 l2:𝕃 a) :
  π (size l1 = n) → π (drop n (l1 ⋅ l2) = l2) ≔
begin
  assume a; induction
  { assume l1 l2 h; simplify;
    have t:π (l1 = □) { apply size0nil l1 h }; rewrite t; reflexivity; }
  { assume n h; induction
    { assume l2 i; apply ⊥ₑ; apply s≠0 [n]; symmetry; apply i; }
    { assume e l1 i l2 j; apply h l1 l2; apply s_inj j; }
  }
end;

opaque symbol drop_drop [a] (l:𝕃 a) n1 n2 :
  π (drop n1 (drop n2 l) = drop (n1 + n2) l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h n1; induction
    { reflexivity; }
    { assume n2 i; simplify; apply h n1 n2; }
  }
end;

// take

symbol take [a] : ℕ → 𝕃 a → 𝕃 a;

rule take 0 _ ↪ □
with take _ □ ↪ □
with take (s $n) ($x ⸬ $l) ↪ $x ⸬ (take $n $l);

assert ⊢ take 3 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 7 ⸬ 2 ⸬ 3 ⸬ □;
assert ⊢ take 10 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □;

opaque symbol take0 [a] (l: 𝕃 a) : π (take 0 l = □) ≔
begin
  reflexivity;
end;

opaque symbol take_cons [a] n (x:τ a) l :
  π (take (s n) (x ⸬ l) = (x ⸬ take n l)) ≔
begin
  assume a l; reflexivity;
end;

opaque symbol take_size [a] (l: 𝕃 a) : π (take (size l) l = l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; simplify; rewrite h; reflexivity; }
end;

opaque symbol take_oversize [a] n (l:𝕃 a) :
  π (istrue (size l ≤ n)) → π (take n l = l) ≔
begin
  assume a; induction
  { assume l h; simplify; symmetry; apply size0nil l; apply ≤0 (size l) h; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; assume j; rewrite h l j; reflexivity; }
  }
end;

opaque symbol cat_take_drop [a] n (l:𝕃 a) : π (take n l ⋅ drop n l = l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; }
  }
end;

opaque symbol size_takel [a] n (l:𝕃 a) :
  π (istrue (n ≤ size l)) → π (size (take n l) = n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { simplify; assume i; apply ⊥ₑ i; }
    { assume e l i; simplify; assume j; apply feq s; apply h l j; }
  }
end;

opaque symbol size_take [a] n (l:𝕃 a) :
  π (size (take n l) = if (n < size l) n (size l)) ≔
begin
abort;

opaque symbol size_take_min [a] n (l:𝕃 a) :
  π (size (take n l) = min n (size l)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; apply feq s (h l); }
  }
end;

opaque symbol take_size_cat [a] n (l1 l2:𝕃 a) :
  π (size l1 = n) → π (take n (l1 ⋅ l2) = l1) ≔
begin
  assume a; induction
  { assume l1 l2 h; simplify; symmetry; apply size0nil l1 h; }
  { assume n h; induction
    { assume l2 i; apply ⊥ₑ; apply s≠0 [n]; symmetry; apply i; }
    { assume e1 l1 i l2 j; simplify; apply feq (λ l, e1 ⸬ l);
      apply h l1 l2; apply ∧ₑ₂ (size_cons e1 n l1) j; 
    }
  }
end;

opaque symbol takel_cat [a] (l1 l2:𝕃 a) n :
  π (istrue (n ≤ size l1)) → π (take n (l1 ⋅ l2) = take n l1) ≔
begin
  assume a; induction
  { assume l2 n h; have t:π (n = 0) { apply ≤0 n h }; rewrite t; reflexivity; }
  { assume e1 l1 h l2; induction
    { reflexivity; }
    { assume n i j; apply feq (λ l:𝕃 a, e1 ⸬ l); apply h l2 n j; }
  }
end;

opaque symbol take_drop [a] m n (l:𝕃 a):
  π (take m (drop n l) = drop n (take (m + n) l)) ≔
begin
  assume a; induction
  { induction
    { reflexivity; }
    { assume m h; induction
      { reflexivity; }
      { assume e l i; simplify; rewrite left .[m in take m l] add0n m;
        rewrite left h l; reflexivity; }
    }
  }
  { assume n h; induction
    { reflexivity; }
    { assume m i; induction
      { reflexivity; }
      { assume e l j; simplify; apply i l; }
    }
  }
end;

opaque symbol takeD [a] m n (l:𝕃 a) :
  π (take (m + n) l = take m l ⋅ take n (drop m l)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; induction
      { reflexivity; }
      { assume e l j; simplify; apply feq (λ l:𝕃 a, e ⸬ l);
        rewrite left addnS; apply h (s n) l; }
    }
  }
end;

opaque symbol takeC [a] (l:𝕃 a) i j:
  π (take i (take j l) = take j (take i l)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; induction
    { reflexivity; }
    { assume i h2; induction
      { reflexivity; }
      { assume j h3; simplify; rewrite h i j; reflexivity; }
    }
  }
end;

// rot

symbol rot [a] n (l:𝕃 a) ≔ drop n l ⋅ take n l;

assert ⊢ rot 2 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 3 ⸬ 1 ⸬ 41 ⸬ 7 ⸬ 2 ⸬ □;

opaque symbol π_rot [a] n (l:𝕃 a) : π (drop n l ⋅ take n l = rot n l) ≔
begin
  reflexivity;
end;

opaque symbol rot0 [a] (l:𝕃 a) : π (rot 0 l = l) ≔
begin
  reflexivity;
end;

opaque symbol size_rot [a] (l:𝕃 a) n0 : π (size (rot n0 l) = size l) ≔
begin
  assume a l n0; simplify; rewrite addnC;
  rewrite left @size_cat a (take n0 l) (drop n0 l);
  rewrite cat_take_drop n0 l; reflexivity; 
end;

opaque symbol rot_oversize [a] n (l:𝕃 a) :
  π (istrue (size l ≤ n)) → π (rot n l = l) ≔
begin
  assume a n l h; simplify; rewrite drop_oversize n l h;
  rewrite take_oversize n l h; reflexivity;
end;

opaque symbol rot_size [a] (l:𝕃 a) : π (rot (size l) l = l) ≔
begin
  assume a l; simplify; rewrite take_size l;
  /*FIXME: Uncaught [File "src/core/infer.ml", line 101
  rewrite @drop_size;*/
  rewrite @drop_size a; reflexivity;
end;

opaque symbol rot_size_cat [a] (l1 l2:𝕃 a) :
  π (rot (size l1) (l1 ⋅ l2) = l2 ⋅ l1) ≔
begin
  assume a l1 l2; simplify; 
  rewrite drop_size_cat (size l1) l1 l2 (eq_refl (size l1));
  rewrite take_size_cat (size l1) l1 l2 (eq_refl (size l1));
  reflexivity;
end;

opaque symbol take_take [a] n m :
  π (istrue (n ≤ m)) → π (`∀ l:𝕃 a, take n (take m l) = take n l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; induction
    { assume i; apply ⊥ₑ i; }
    { assume m i j; induction
      { reflexivity; }
      { assume e l k; simplify; apply feq (λ l:𝕃 a, e ⸬ l) (h m j l); }
    }
  }
end;

// rotr

symbol rotr [a] n (l:𝕃 a) ≔ rot (size l - n) l;

assert ⊢ rotr 2 (7 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 41 ⸬ □) ≡ 1 ⸬ 41 ⸬ 7 ⸬ 2 ⸬ 3 ⸬ □;

opaque symbol π_rotr [a] n (l:𝕃 a) :
  π (drop (size l - n) l ⋅ take (size l - n) l = rotr n l) ≔
begin
  reflexivity;
end;

opaque symbol rotr0 [a] (l:𝕃 a) : π (rotr 0 l = l) ≔
begin
  assume a l; simplify; rewrite take_size l; rewrite @drop_size a; //FIXME
  reflexivity;
end;

opaque symbol rotK [a] n (l:𝕃 a) : π (rot n (rotr n l) = l) ≔
begin
abort;

opaque symbol rot_inj [a] n (l1 l2:𝕃 a) :
  π (rot n l1 = rot n l2) → π (l1 = l2) ≔
begin
abort;

// membership

symbol ∈ [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → 𝔹;

rule ∈ _ _ □ ↪ false
with ∈ $beq $x ($y ⸬ $l) ↪ $beq $x $y or ∈ $beq $x $l;

opaque symbol in_cons [a] beq (x y:τ a) l :
  π (∈ beq x (y ⸬ l) = beq x y or ∈ beq x l) ≔
begin
  assume a beq x y; induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

opaque symbol in_nil [a] beq (x:τ a) : π (∈ beq x □ = false) ≔
begin
  assume a beq x; reflexivity;
end;

opaque symbol mem_seq1 [a] beq (x y:τ a) :
  π (∈ beq x (y ⸬ □) = (beq x y)) ≔
begin
  assume a beq x y; reflexivity;
end;

opaque symbol mem_cat [a] beq (x:τ a) l1 l2 :
  π (∈ beq x (l1 ⋅ l2) = ∈ beq x l1 or ∈ beq x l2) ≔
begin
  assume a beq x; induction
  { reflexivity; }
  { assume e1 l1 h; simplify; assume l2; rewrite h l2; rewrite orA;
    reflexivity; }
end;

opaque symbol mem_head [a] beq (x:τ a) l :
  π (beq x x = true) → π (istrue (∈ beq x (x ⸬ l))) ≔
begin
  assume a beq x l hrefl; simplify; rewrite hrefl; apply top;
end;

opaque symbol mem_take [a] beq n l (x:τ a) :
  π (istrue (∈ beq x (take n l))) → π (istrue (∈ beq x l)) ≔
begin
  assume a beq n l x h; rewrite left cat_take_drop n l;
  rewrite mem_cat beq x (take n l) (drop n l);
  refine @orᵢ₁ (∈ beq x (take n l)) (∈ beq x (drop n l)) h;
end;

opaque symbol mem_drop [a] beq n l (x:τ a) :
  π (istrue (∈ beq x (drop n l))) → π (istrue (∈ beq x l)) ≔
begin
  assume a beq n l x h; rewrite left cat_take_drop n l;
  rewrite mem_cat beq x (take n l) (drop n l);
  refine @orᵢ₂ (∈ beq x (take n l)) (∈ beq x (drop n l)) h;
end;

// index

symbol index [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → ℕ;

rule index _ _ □ ↪ 0
with index $beq $x ($y ⸬ $l) ↪ if ($beq $x $y) 0 (s (index $beq $x $l));

assert ⊢ index eqn 2 (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ 1;
assert ⊢ index eqn 26 (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ 4;

opaque symbol index_size [a] beq (x:τ a) l :
  π (istrue (index beq x l ≤ size l)) ≔
begin
  assume a beq x; induction
  { apply top; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ b, istrue (if b 0 (s (index beq x l)) ≤ s (size l))) _ _ (beq x e) {
      apply top;
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol index_head [a] beq (x:τ a) l :
  π (beq x x = true) → π (index beq x (x ⸬ l) = 0) ≔
begin
  assume a beq x l hrefl; simplify; rewrite hrefl; reflexivity;
end;

// has

symbol has [a] : (τ a → 𝔹) → 𝕃 a → 𝔹;

rule has _ □ ↪ false
with has $p ($x ⸬ $l) ↪ if ($p $x) true (has $p $l);

assert ⊢ has (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ true;
assert ⊢ has (λ x, eqn (x + 1) 3) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ false;

// all

symbol all [a] : (τ a → 𝔹) → 𝕃 a → 𝔹;

rule all _ □ ↪ true
with all $p ($x ⸬ $l) ↪ if ($p $x) (all $p $l) false;

assert ⊢ all (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ false;
assert ⊢ all (λ x, eqn (x + 1) 3) (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ true;

// find

symbol find [a] : (τ a → 𝔹) → 𝕃 a → ℕ;

rule find _ □ ↪ 0
with find $p ($x ⸬ $l) ↪ if ($p $x) 0 (s (find $p $l));

assert ⊢ find (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ 1;
assert ⊢ find (λ x, eqn (x + 1) 3) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ 4;

opaque symbol find_size [a] (p:τ a → 𝔹) l :
  π (istrue (find p l ≤ size l)) ≔
begin
  assume a p; induction
  { apply top; }
  { assume e l h;
    refine ind_𝔹 (λ x:𝔹, istrue (if x 0 (s (find p l)) ≤ s (size l))) _ _ (p e) {
      apply top;
    } {
      simplify; apply h;
    };
  }
end;

// count

symbol count [a] : (τ a → 𝔹) → 𝕃 a → ℕ;

rule count _ □ ↪ 0
with count $p ($x ⸬ $l) ↪ if ($p $x) (s (count $p $l)) (count $p $l);

assert ⊢ count (λ x, eqn (x + 1) 3) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ 0;
assert ⊢ count (λ x, eqn (x + 1) 3) (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ 4;

opaque symbol count_size [a] (p:τ a → 𝔹) l : π(istrue (count p l ≤ size l)) ≔
begin
  assume a p; induction
  { apply top; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ x:𝔹, istrue (if x (s (count p l)) (count p l) ≤ s (size l))) _ _ (p e) {
      simplify; apply h;
    } {
      simplify;
      refine @leq_trans (count p l) (size l) (s (size l)) h (leqnSn (size l)); 
    };
  }
end;

// count_mem

symbol count_mem [a] (beq : τ a → τ a → 𝔹) e ≔ count (beq e);

assert ⊢ count_mem eqn 2 (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ 0;
assert ⊢ count_mem eqn 2 (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ 4;

// is_constant

symbol is_constant [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝔹;

rule is_constant _ □ ↪ true
with is_constant $beq ($x ⸬ $l) ↪ if (all ($beq $x) $l) true false;

assert ⊢ is_constant eqn (2 ⸬ 2 ⸬ 2 ⸬ 2 ⸬ □) ≡ true;
assert ⊢ is_constant eqn □ ≡ true;
assert ⊢ is_constant eqn (2 ⸬ 2 ⸬ 2 ⸬ 1 ⸬ □) ≡ false;

// uniq

symbol uniq [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝔹;

rule uniq _ □ ↪ true
with uniq $beq ($x ⸬ $l) ↪ if (not (∈ $beq $x $l)) (uniq $beq $l) false;

assert ⊢ uniq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ true;
assert ⊢ uniq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ false;

// subseq

symbol subseq [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule subseq _ □ □ ↪ true
with subseq _ □ (_ ⸬ _) ↪ false
with subseq _ (_ ⸬ _) □ ↪ false
with subseq $beq ($x ⸬ $l1) ($y ⸬ $l2)
     ↪ if ($beq $x $y) (subseq $beq $l1 $l2) false;

assert ⊢ subseq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ false;
assert ⊢ subseq eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) ≡ true;

// is_prefix

symbol is_prefix [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule is_prefix _ □ _ ↪ true
with is_prefix _ (_ ⸬ _) □ ↪ false
with is_prefix $beq ($x ⸬ $l1) ($y ⸬ $l2)
     ↪ if ($beq $x $y) (is_prefix $beq $l1 $l2) false;

assert ⊢ is_prefix eqn (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ true;

// is_suffix

symbol is_suffix [a] beq l1 l2 ≔ @is_prefix a beq (rev l1) (rev l2);

assert ⊢ is_suffix eqn (4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ true;

// is_infix

symbol is_infix [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule is_infix _ □ _ ↪ true
with is_infix _ (_ ⸬ _) □ ↪ false
with is_infix $beq ($x ⸬ $l1) ($y ⸬ $l2)
     ↪ if ($beq $x $y) (is_prefix $beq $l1 $l2) (is_infix $beq ($x ⸬ $l1) $l2);

assert ⊢ is_infix eqn (51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ true;

// infix_index

symbol infix_index [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → ℕ;

rule infix_index _ □ _ ↪ 0
with infix_index _ (_ ⸬ _) □ ↪ 0
with infix_index $beq ($x ⸬ $l1) ($y ⸬ $l2) ↪
  if ($beq $x $y)
    (if (is_prefix $beq $l1 $l2) 0 (s (size $l2)))
    (s (infix_index $beq ($x ⸬ $l1) $l2));

assert ⊢ infix_index eqn (51 ⸬ 3 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ 2;
assert ⊢ infix_index eqn (51 ⸬ 4 ⸬ □) (42 ⸬ 4 ⸬ 51 ⸬ 3 ⸬ 4 ⸬ □) ≡ 5;

// perm_eq

symbol perm_eq [a] beq l1 l2
  ≔ @all a (λ x, eqn (count_mem beq x l1) (count_mem beq x l2)) (l1 ⋅ l2);

assert ⊢ perm_eq eqn (59 ⸬ 58 ⸬ 4 ⸬ 2 ⸬ □) (58 ⸬ 4 ⸬ 2 ⸬ 59 ⸬ □) ≡ true;
assert ⊢ perm_eq eqn (59 ⸬ 58 ⸬ 4 ⸬ 2 ⸬ □) (58 ⸬ 4 ⸬ 2 ⸬ 69 ⸬ □) ≡ false;

// filter

symbol filter [a] : (τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule filter _ □ ↪ □
with filter $p ($x ⸬ $l) ↪ if ($p $x) ($x ⸬ (filter $p $l)) (filter $p $l);

assert ⊢ filter (λ x, eqn (x + 1) 3) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ 2 ⸬ 68 ⸬ □) ≡ 2 ⸬ 2 ⸬ □;

symbol rmfilter [a] : (τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule rmfilter _ □ ↪ □
with rmfilter $p ($x ⸬ $l) ↪ if ($p $x) (filter $p $l) ($x ⸬ (filter $p $l));

opaque symbol size_filter [a] (p:τ a → 𝔹) l :
  π (size (filter p l) = count p l) ≔
begin
  assume a p; induction
  { reflexivity; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ x, size (if x (e ⸬ filter p l) (filter p l)) = (if x (s (count p l)) (count p l))) _ _ (p e) {
      simplify; apply feq s h;
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol filter_cat [a] (p:τ a → 𝔹) l1 l2 :
  π (filter p (l1 ⋅ l2) = filter p l1 ⋅ filter p l2) ≔
begin
  assume a p; induction
  { reflexivity; }
  { assume e1 l1 h l2; simplify;
    refine ind_𝔹 (λ x, if x (e1 ⸬ filter p (l1 ⋅ l2)) (filter p (l1 ⋅ l2)) = if x (e1 ⸬ filter p l1) (filter p l1) ⋅ filter p l2) _ _ (p e1) {
      simplify; rewrite h l2; reflexivity;
    } {
      simplify; rewrite h l2; reflexivity;
    }
  }
end;

opaque symbol filter_rev [a] (p:τ a → 𝔹) l :
  π (filter p (rev l) = rev (filter p l)) ≔
begin
  assume a p; induction
  { reflexivity; }
  { assume e l h; simplify; rewrite filter_cat p (rev l) (e ⸬ □); simplify;
    refine ind_𝔹 (λ b:𝔹, (filter p (rev l) ⋅ (if b (e ⸬ □) □) = rev (if b (e ⸬ filter p l) (filter p l)))) _ _ (p e) {
      simplify; rewrite h; reflexivity;
    } {
      simplify; rewrite h; reflexivity;
    };
  }
end;

opaque symbol count_cat [a] (p:τ a → 𝔹) l1 l2 :
  π (count p (l1 ⋅ l2) = count p l1 + count p l2) ≔
begin
  assume a p l1 l2; rewrite left size_filter p l1;
  rewrite left size_filter p l2; rewrite left size_filter p (l1 ⋅ l2);
  rewrite filter_cat p l1 l2;
  rewrite left size_cat (filter p l1) (filter p l2); reflexivity;
end;

opaque symbol eq_find [a] beq p (l1 l2:𝕃 a) :
  π (istrue (eql beq l1 l2)) → π (istrue (eqn (find p l1) (find p l2))) ≔
begin
abort;

// undup

symbol undup [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a;

rule undup _ □ ↪ □
with undup $beq ($x ⸬ $l)
  ↪ if (∈ $beq $x (undup $beq $l)) (undup $beq $l) ($x ⸬ (undup $beq $l));

assert ⊢ undup eqn (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ 2 ⸬ 3 ⸬ □) ≡ 42 ⸬ 51 ⸬ 2 ⸬ 3 ⸬ □;

opaque symbol size_undup [a] beq (l:𝕃 a) :
  π (istrue (size (undup beq l) ≤ size l)) ≔
begin
  assume a beq; induction
  { apply top; }
  { assume e l h; simplify;
    refine ind_𝔹 (λ x, istrue (size (if x (undup beq l) (e ⸬ undup beq l)) ≤ s (size l))) _ _ (∈ beq e (undup beq l)) {
      simplify;
      refine @leq_trans (size (undup beq l)) (size l) (s (size l)) h (leqnSn (size l));
    } {
      simplify; apply h;
    };
  }
end;

opaque symbol undup_uniq [a] beq (l:𝕃 a) :
  π (istrue (uniq beq (undup beq l))) ≔
begin
  assume a beq; induction
  { apply top; }
  { assume e l h; simplify;
    refine ind_𝔹_eq (λ b, (istrue(uniq beq (if b (undup beq l) (e ⸬ (undup beq l)))))) (∈ beq e (undup beq l)) _ _ {
      assume i; rewrite i; simplify; apply h;
    } {
      assume i; rewrite i; simplify; rewrite i; simplify; apply h; 
    }; 
  }
end;

opaque symbol filter_undup [a] beq p (l:𝕃 a) :
  π (filter p (undup beq l) = undup beq (filter p l)) ≔
begin
abort;

opaque symbol count_undup [a] beq p (l:𝕃 a) :
  π (istrue (count p (undup beq l) ≤ count p l)) ≔
begin
abort;

// map

symbol map [a b] : (τ a → τ b) → 𝕃 a → 𝕃 b;

rule map _ □ ↪ □
with map $f ($x ⸬ $l) ↪ $f $x ⸬ map $f $l;

assert ⊢ map (λ x, 3 ≤ x) (42 ⸬ 2 ⸬ 51 ⸬ 3 ⸬ □) ≡ true ⸬ false ⸬ true ⸬ true ⸬ □;

opaque symbol map_cons [a b] (f:τ a → τ b) l x :
  π (map f (x ⸬ l) = f x ⸬ map f l) ≔
begin
  assume a b f l x; reflexivity;
end;

opaque symbol map_cat [a b] (f:τ a → τ b) l1 l2 :
  π (map f (l1 ⋅ l2) = map f l1 ⋅ map f l2) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e1 l1 h l2; simplify; rewrite h l2; reflexivity; }
end;

opaque symbol size_map [a b] (f:τ a → τ b) l : π (size (map f l) = size l) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h; simplify; apply feq s h; }
end;

opaque symbol behead_map [a b] (f:τ a → τ b) l :
  π (behead (map f l) = map f (behead l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

opaque symbol map_rcons [a b] (f:τ a → τ b) l e :
  π (map f (rcons l e) = rcons (map f l) (f e)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume x l h e; simplify; rewrite h e; reflexivity; }
end;

opaque symbol last_map [a b] (f:τ a → τ b) l x :
  π (last (f x) (map f l) = f (last x l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h x; simplify; rewrite h e; reflexivity; }
end;

opaque symbol belast_map [a b] (f:τ a → τ b) l x :
  π (belast (f x) (map f l) = map f (belast x l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h x; simplify; rewrite h e; reflexivity; }
end;

opaque symbol map_take [a b] (f:τ a → τ b) n l :
  π (map f (take n l) = take n (map f l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; } 
  }
end;

opaque symbol map_drop [a b] (f:τ a → τ b) n l :
  π (map f (drop n l) = drop n (map f l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume n h; induction
    { reflexivity; }
    { assume e l i; simplify; rewrite h l; reflexivity; } 
  }
end;

opaque symbol map_rot [a b] (f:τ a → τ b) n l :
  π (map f (rot n l) = rot n (map f l)) ≔
begin
  assume a b f n l; simplify; rewrite map_cat f (drop n l) (take n l);
  rewrite map_take f n l; rewrite map_drop f n l; reflexivity; 
end;

opaque symbol map_rotr [a b] (f:τ a → τ b) n l :
  π (map f (rotr n l) = rotr n (map f l)) ≔
begin
  assume a b f n l; simplify;
  rewrite map_cat f (drop (size l - n) l) (take (size l - n) l);
  rewrite map_drop f (size l - n) l; rewrite map_take f (size l - n) l;
  rewrite size_map f l; reflexivity;
end;

opaque symbol map_rev [a b] (f:τ a → τ b) l :
  π (map f (rev l) = rev (map f l)) ≔
begin
  assume a b f; induction
  { reflexivity; }
  { assume e l h; simplify; rewrite map_cat f (rev l) (e ⸬ □); rewrite h;
    reflexivity; }
end;

opaque symbol inj_map [a b] (f:τ a → τ b) :
  (Π x y, π(f x = f y) → π(x = y)) →
  Π l1 l2, π (map f l1 = map f l2) → π (l1 = l2) ≔
begin
  assume a b f h; induction
  { induction
    { reflexivity; }
    { simplify; assume e l i j; apply ⊥ₑ (□≠⸬ j) }
  }
  { assume e1 l1 i; induction
    { assume j; apply ⊥ₑ (⸬≠□ j) }
    {
      simplify; assume e2 l2 j k; refine feq2 (⸬) _ _
      { apply h; apply ∧ₑ₁ (⸬_inj k) }
      { apply i; apply ∧ₑ₂ (⸬_inj k) }
    }
  }
end;

// sumn

symbol sumn : 𝕃 nat → ℕ;

rule sumn □ ↪ 0
with sumn ($x ⸬ $l) ↪ $x + sumn $l;

assert ⊢ sumn (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 6;

// prodn

symbol prodn : 𝕃 nat → ℕ;

rule prodn □ ↪ 1
with prodn ($x ⸬ $l) ↪ $x * prodn $l;

assert ⊢ prodn (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 3 !;
