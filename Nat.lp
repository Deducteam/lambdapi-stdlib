/* Library on natural numbers

following https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/ssrnat.v

(lemmas with unfinished proofs:
ltn_neqAle, leq_eqVlt, gtn_max, geq_max, minnE, expn_gt0, ltn_expl). */

require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.FOL Blanqui.Lib.Eq
  Blanqui.Lib.Bool;

inductive ℕ : TYPE ≔
| zero : ℕ
| s : ℕ → ℕ;

// enable decimal notation

builtin "0"  ≔ zero;
builtin "+1" ≔ s;

assert ⊢ 42 : ℕ;

// set code for ℕ

constant symbol nat : Set;

rule τ nat ↪ ℕ;

symbol is0 : ℕ → 𝔹;

// non confusion of constructors

rule is0 0 ↪ true
with is0 (s _) ↪ false;

opaque symbol s≠0 [n] : π (s n ≠ 0) ≔
begin
  assume n h; refine ind_eq h (λ n, istrue(is0 n)) top
end;

opaque symbol 0≠s [n] : π (0 ≠ s n) ≔
begin
  assume n h; apply @s≠0 n; symmetry; apply h
end;

// boolean equality on ℕ

symbol =ℕ : ℕ → ℕ → 𝔹; notation =ℕ infix 10;

rule 0 =ℕ 0 ↪ true
with s $x =ℕ s $y ↪ $x =ℕ $y
with 0 =ℕ s _ ↪ false
with s _ =ℕ 0 ↪ false;

opaque symbol =ℕ_correct x y : π(istrue(x =ℕ y)) → π(x = y) ≔
begin
  induction
  { induction { reflexivity; } { assume x h i; apply ⊥ₑ i; } }
  { assume x h; induction
    { assume i; apply ⊥ₑ i; }
    { assume y i j; apply feq s; apply h _ j; }
  }
end;

opaque symbol =ℕ_complete x y : π(x = y) → π(istrue(x =ℕ y)) ≔
begin
  induction
  { assume y i; rewrite left i; apply top; }
  { simplify; assume x h; /*FIXME: x0 is replaced by x!*/ induction
    { assume i; apply s≠0 i; }
    { assume y i j; simplify; }
  }
abort;

// predecessor

symbol p : ℕ → ℕ;

rule p 0 ↪ 0
with p (s $x) ↪ $x;

opaque symbol s_inj [x y] : π (s x = s y) → π (x = y) ≔
begin
  assume x y h; apply feq p h
end;

// addition

symbol + : ℕ → ℕ → ℕ; notation + infix left 20;

assert x y z ⊢ x + y + z ≡ (x + y) + z;

rule 0 + $y ↪ $y
with s $x + $y ↪ s ($x + $y);

opaque symbol add0n x : π (0 + x = x) ≔
begin
  assume x; reflexivity;
end;

opaque symbol addn0 x : π (x + 0 = x) ≔
begin
  induction
  { reflexivity }
  { assume x' h; simplify; rewrite h; reflexivity }
end;

rule $x + 0 ↪ $x;

opaque symbol addSn x y : π (s x + y = s (x + y)) ≔
begin
  assume x; reflexivity;
end;

opaque symbol addnS x y : π (x + s y = s (x + y)) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite h; reflexivity }
end;

rule $x + s $y ↪ s ($x + $y);

opaque symbol add1n n : π (1 + n = s n) ≔
begin
  assume n; reflexivity;
end;

opaque symbol addn1 n : π (n + 1 = s n) ≔
begin
  assume n; reflexivity;
end;

opaque symbol addSnnS m n : π (s m + n = m + s n) ≔
begin
  assume m n; reflexivity;
end;

opaque symbol addnC x y : π (x + y = y + x) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite h; reflexivity }
end;

opaque symbol addnA x y z : π ((x + y) + z = x + (y + z)) ≔
begin
  induction
  { reflexivity }
  { assume x' h y z; simplify; rewrite h; reflexivity }
end;

rule ($x + $y) + $z ↪ $x + ($y + $z);

opaque symbol addnCA m n p : π ((m + n) + p = (m + p) + n) ≔
begin
  assume m n p; symmetry; rewrite addnA; rewrite .[p + n] addnC;
  rewrite left addnA; reflexivity;
end;

opaque symbol addnAC m n p : π (m + (n + p) = n + (m + p)) ≔
begin
  assume m n p; symmetry; rewrite left addnA; rewrite .[n + m] addnC;
  rewrite addnA; reflexivity; 
end;

opaque symbol addnCAC m n p : π (m + n + p = p + n + m) ≔
begin
  assume m n p; rewrite addnC; rewrite .[m + _] addnC; rewrite addnA;
  reflexivity; 
end;

opaque symbol addnACl m n p : π (m + n + p = n + (p + m)) ≔
begin
  assume m n p; rewrite .[m + _] addnC; rewrite addnA; rewrite .[m + _] addnC;
  reflexivity;
end;

opaque symbol addnACA m n p q : π ((m + n) + (p + q) = (m + p) + (n + q)) ≔
begin
  assume m n p q; simplify; rewrite left .[p + (n + q)] addnA;
  rewrite .[p + n] addnC; rewrite .[(n + p) + q] addnA; reflexivity; 
end;

opaque symbol addnI x y z : π (z + x = z + y) → π (x = y) ≔
begin
  assume x y; induction
  { assume h; apply h;}
  { assume z h i; apply h; apply s_inj; apply i;}
end;

opaque symbol addIn x y z : π (x + z = y + z) → π (x = y) ≔
begin
  assume x y; induction
  { assume h; apply h;}
  { assume z h i; apply h; apply s_inj; apply i;}
end;

opaque symbol addn_eq0 m n : π (m + n = 0 ⇔ m = 0 ∧ n = 0) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume m h; apply ∧ᵢ (eq_refl 0) h; }
    { assume m h n i; apply ⊥ₑ (s≠0 i) }
  } {
    generalize m; induction
    { assume n h; apply ∧ₑ₂ h }
    { assume m h n i; apply ⊥ₑ (s≠0 (∧ₑ₁ i)) }
  }
end;

opaque symbol eqn_add2l p m n : π ((p + m = p + n) ⇔ (m = n)) ≔
begin
  assume p m n;
  apply ∧ᵢ {
    refine addnI m n p
  } {
    //FIXME: generalize p fails
    generalize m; generalize p; induction
    { assume m n h; apply h }
    { assume z h m n i; simplify; rewrite h m n i; reflexivity }  
  };
end;

opaque symbol eqn_add2r p m n : π ((m + p = n + p) ⇔ (m = n)) ≔
begin
  assume p m n; rewrite addnC m p; rewrite addnC n p; apply eqn_add2l p m n;
end;

// substraction

symbol - : ℕ → ℕ → ℕ; notation - infix left 20;

rule 0 - _ ↪ 0
with $x - 0 ↪ $x
with (s $x) - (s $y) ↪ $x - $y;

opaque symbol sub0n n : π (n - 0 = n) ≔
begin
  reflexivity;
end;

opaque symbol subn0 n : π (0 - n = 0) ≔
begin
  reflexivity;
end;

opaque symbol subnn x : π (x - x = 0) ≔
begin
  induction
  { reflexivity }
  { assume x h; simplify; apply h;}
end;

rule $x - $x ↪ 0;

opaque symbol subSS m n : π (s m - s n = m - n) ≔
begin
  reflexivity;
end;

opaque symbol subn1 n : π (n - 1 = p n) ≔
begin
  induction
  { reflexivity; }
  { assume n h; reflexivity;  }
end;

opaque symbol subnS x y : π (x - s y = p (x - y)) ≔
begin
  induction
  { reflexivity; }
  { assume x h; induction
    { reflexivity; }
    { assume y i; simplify; rewrite h; reflexivity }
  }
end;

opaque symbol subSnn n : π (s n - n = 1) ≔
begin
  induction
  { reflexivity; }
  { assume n h; simplify; apply h; }
end;

opaque symbol predn_sub x y : π (p (x - y) = p x - y) ≔
begin
  induction
  { reflexivity; }
  { assume x h; induction
    { reflexivity; }
    { assume y i; simplify; symmetry; rewrite subnS; reflexivity; }
  }
end;

opaque symbol subnAC z x y : π ((x - y) - z = (x - z) - y) ≔
begin
  induction
  { reflexivity; }
  { assume z h; induction
    { reflexivity; }   
    { assume x i; induction
      { reflexivity; }
      { assume y j; simplify; rewrite i; rewrite subnS; symmetry;
        rewrite subnS; rewrite predn_sub; reflexivity}
    }
  }
end;

opaque symbol addnK x y : π (x + y - y = x) ≔
begin
  induction
  { reflexivity; }
  { assume x h; induction
    { reflexivity; }
    { simplify; assume y i; rewrite i; reflexivity; }
  }
end;

opaque symbol subnDA x y z : π (x - (y + z) = (x - y) - z) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; rewrite subnS; symmetry; rewrite subnS;
        rewrite h; reflexivity; }
    }
  }
end;

opaque symbol subnDl z x y : π ((z + x) - (z + y) = x - y) ≔
begin
  induction
  { reflexivity }
  { assume z h; induction
    { assume y; simplify; rewrite subnDA; reflexivity; }
    { assume x i; induction
      { rewrite addnC; rewrite addn0; rewrite addnK; reflexivity; }
      { assume y j; rewrite addnC; rewrite subnDA; rewrite addnK; reflexivity }
    }
  }
end;

opaque symbol subnDr z x y : π ((x + z) - (y + z) = x - y) ≔
begin
  assume z x y; rewrite addnC; rewrite .[y + _] addnC; rewrite subnDl;
  reflexivity;
end;

opaque symbol subSKn m n : π (p (s m - n) = m - n) ≔
begin
  assume m n; rewrite left subnS; reflexivity;
end;

// multiplication

symbol * : ℕ → ℕ → ℕ; notation * infix left 30; // \times

assert x y z ⊢ x + y * z ≡ x + (y * z);

rule 0 * _  ↪ 0
with s $x * $y ↪ $y + $x * $y;

opaque symbol mul0n x : π (x * 0 = 0) ≔
begin
  induction { reflexivity } { assume x' h; apply h }
end;

rule _ * 0 ↪ 0;

opaque symbol muln0 x : π (0 * x = 0) ≔
begin
  assume x; reflexivity;
end;

opaque symbol mul1n n : π (1 * n = n) ≔
begin
  assume n; reflexivity;
end;

opaque symbol muln1 n : π (n * 1 = n) ≔
begin
  induction
  { reflexivity; }
  { assume n h; simplify; rewrite h; reflexivity; }
end;

opaque symbol mulSn m n : π (s m * n = n + m * n) ≔
begin
  reflexivity;
end;

opaque symbol mulSnr m n : π (s m * n = m * n + n) ≔
begin
  assume m n; rewrite addnC; reflexivity;
end;

opaque symbol mulnS x y : π (x * s y = x + x * y) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite h; rewrite addnAC; reflexivity }
end;

//rule $x * s $y ↪ $x + $x * $y; is confluent modulo C only

opaque symbol mulnSr x y : π (x * s y = x * y + x) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite mulnS; rewrite .[x' + _] addnC;
    reflexivity }
end;

//rule $x * s $y ↪ $x * $y + $x; is confluent modulo C only

opaque symbol mulnC x y : π (x * y = y * x) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite mulnS; rewrite h; reflexivity }
end;

opaque symbol mulnDl x y z : π ((x + y) * z = x * z + y * z) ≔
begin
  induction
  { reflexivity }
  { assume x' h y z; simplify; rewrite h; reflexivity }
end;

//rule ($x + $y) * $z ↪ $x * $z + $y * $z; is confluent modulo AC only

opaque symbol mulnDr x y z : π (z * (x + y) = z * x + z * y) ≔
begin
  assume x y z; rewrite mulnC; rewrite mulnDl; rewrite mulnC;
  rewrite .[y * _] mulnC; reflexivity
end;

//rule $z * ($x + $y) ↪ $z * $x + $z * $y; is confluent modulo AC only

opaque symbol mulnBr x y z : π (x * (y - z) = x * y - x * z) ≔
begin
  induction
  { reflexivity; }
  { assume x h; induction
    { reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; simplify; rewrite mulnS; rewrite mulnS;
        rewrite left addnAC; rewrite .[z + (x + _)] addnAC; 
        rewrite subnDl; rewrite left mulSn; rewrite left mulSn;
        rewrite left mulSn; rewrite left i; reflexivity; }
    }
  }
end;

opaque symbol mulnBl x y z : π ((x - y) * z = x * z - y * z) ≔
begin
  assume x y z; rewrite mulnC; rewrite .[x * z] mulnC; rewrite .[y * z] mulnC;
  rewrite left mulnBr; reflexivity;
end;

opaque symbol mulnA x y z : π ((x * y) * z = x * (y * z)) ≔
begin
  induction
  { reflexivity }
  { assume x' h y z; simplify; rewrite mulnDl; rewrite h; reflexivity }
end;

//rule ($x * $y) * $z ↪ $x * ($y * $z); is not confluent

opaque symbol mulnCA x y z: π (x * (y * z) = y * (x * z)) ≔
begin
  assume x y z; rewrite left mulnA; rewrite .[x * y] mulnC; rewrite mulnA;
  reflexivity;
end;

opaque symbol mulnAC x y z: π ((x * y) * z = (x * z) * y) ≔
begin
  assume x y z; rewrite mulnA; rewrite .[y * z] mulnC; rewrite left mulnA;
  reflexivity;
end;

opaque symbol mulnACA x y z t: π ((x * y) * (z * t) = (x * z) * (y * t)) ≔
begin
  assume x y z t; rewrite mulnA; rewrite .[y * _] mulnCA; rewrite mulnA;
  reflexivity;
end;

opaque symbol muln_eq0 m n : π (m * n = 0 ⇔ m = 0 ∨ n = 0) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n h; apply ∨ᵢ₁ h; }
    { assume m h n i; 
      have t: π (n = 0 ∧ (m * n) = 0) { apply ∧ₑ₁ (addn_eq0 n (m * n)) i; }; 
      have u: π (n = 0) { apply ∧ₑ₁ t; };
      apply ∨ᵢ₂ u;
    }
  } {
    assume h;
    refine ∨ₑ h _ _ {
      assume i; rewrite i; reflexivity;
    } {
      assume i; rewrite i; reflexivity;
    };
  };
end;

// order on ℕ

symbol ≤ : ℕ → ℕ → 𝔹; notation ≤ infix left 10;

rule 0 ≤ _ ↪ true
with s _ ≤ 0 ↪ false
with s $x ≤ s $y ↪ $x ≤ $y;

symbol < : ℕ → ℕ → 𝔹; notation < infix 10;

rule $x < $y ↪ s $x ≤ $y;

symbol ≥ : ℕ → ℕ → 𝔹; notation ≥ infix 10;

rule $x ≥ $y ↪ $y ≤ $x;

symbol > : ℕ → ℕ → 𝔹; notation > infix 10;

rule $x > $y ↪ s $y ≤ $x;

opaque symbol ≤0 x : π (istrue (x ≤ 0)) → π (x = 0) ≔
begin
  induction
  { assume h; reflexivity;}
  { assume x h i; apply ⊥ₑ; apply i; }
end;

opaque symbol ≤_refl x : π (istrue (x ≤ x)) ≔
begin
  induction
  { simplify; apply top;}
  { assume x h; simplify; apply h; }
end;

opaque symbol eq_leq x y : π (x = y) → π (istrue (x ≤ y)) ≔
begin 
  assume x y h; rewrite h; apply ≤_refl y;
end;

opaque symbol leq_trans [x y z] : π (istrue (x ≤ y)) → π (istrue (y ≤ z)) → π (istrue (x ≤ z)) ≔
begin
  induction
  { assume y z h i; apply h; }
  { assume x h; induction
    { assume y i; apply ⊥ₑ i; }
    { assume y i; induction
      { assume j k; apply k; }
      { assume z j k l; apply h y z k l; }
    }
  }
end;

opaque symbol eqn_leq x y : π (istrue (x ≤ y) ∧ istrue (y ≤ x) ⇔ (x = y)) ≔
begin
  assume x y; apply ∧ᵢ {
    generalize x; induction
    { assume y g; 
      have i: π (istrue (y ≤ 0)) { apply ∧ₑ₂ g; };
      symmetry; apply ≤0 y i;
    }
    {
      assume x h; induction
      { assume g; 
        have i: π (istrue (s x ≤ 0)) { apply ∧ₑ₁ g; };
        apply ≤0 (s x) i;
      }
      { assume y i j; apply feq s; apply h y j;}
    }
  } {
    assume h;
    have t: π (istrue (x ≤ y)) { apply eq_leq _ _ h;};
    have u: π (istrue (y ≤ x)) { apply eq_leq y x _; symmetry; apply h;};
    apply ∧ᵢ t u;
  };
end;

opaque symbol leqsnn n: π (istrue (s n ≤ n)) → π ⊥ ≔
begin
  induction
  { assume h; apply h; }
  { assume n h i; apply h; apply i;}
end;

opaque symbol letnS m n : π (istrue (m < s n)) → π (istrue (m ≤ n)) ≔
begin
  assume m n h; apply h;
end;

opaque symbol ltn0 n : π (istrue (n < 0)) → π ⊥ ≔
begin
  assume n h; apply h;
end;

opaque symbol ltnn n : π (istrue (n < n)) → π ⊥ ≔
begin
  assume n h; apply leqsnn n; apply h;
end;

opaque symbol ltnSn n : π (istrue (n < s n)) ≔
begin
  assume n; simplify; apply ≤_refl n;
end;

opaque symbol leq0n n : π (istrue (0 ≤ n)) ≔
begin
  induction
  { apply ≤_refl 0;}
  { assume n h; simplify; apply h; }
end;

opaque symbol ltn0Sn n : π (istrue (0 < s n)) ≔
begin
  assume n; apply leq0n n;
end;

opaque symbol leqnSn n : π (istrue (n ≤ s n)) ≔
begin
  induction
  { apply leq0n 1; }
  { assume n h; simplify; apply h; }
end;

opaque symbol leq_pred n : π (istrue (p n ≤ n)) ≔
begin
  induction
  { apply top;}
  { assume n h; simplify; apply leqnSn n;} 
end;

opaque symbol ltnW m n : π (istrue (m < n)) → π (istrue (m ≤ n)) ≔
begin
  induction
  { assume m h; apply top;}
  { assume m h; induction
    { assume i; apply i;}
    { assume n i j; apply h n; apply j;}
  }
end;

opaque symbol leqW m n : π (istrue (m ≤ n)) → π (istrue (m ≤ s n)) ≔
begin
  assume m n h; apply ltnW m (s n); simplify; apply h;
end;

opaque symbol ltn_trans x y z : π (istrue (x < y)) → π (istrue (y < z)) → π (istrue (x < z)) ≔
begin
  assume x y z h i;
  have v:π (istrue (s x ≤ s y)) { apply leqW (s x) y h; };
  apply @leq_trans (s x) (s y) z v i; //FIXME
end;

opaque symbol <_asym x y : π (istrue (x < y)) → π (¬ (istrue (y < x))) ≔
begin
  assume x y h i;
  have t:π (istrue (y ≤ s y)) { apply leqnSn y; };
  have u:π (istrue (s x ≤ s y)) { apply @leq_trans (s x) y (s y) h t; }; 
  have v:π (istrue (s x ≤ x)) { apply @leq_trans (s x) (s y) x u i; };
  apply leqsnn x; apply v;
end;

opaque symbol anti_ltn x y : π(istrue (x < y)) → π(istrue (y < x)) → π(x = y) ≔
begin
  assume x y h i;
  have c:π (istrue (x ≤ s x)) { apply leqnSn x; };
  have d:π (istrue (y ≤ s y)) { apply leqnSn y; };
  have e:π (istrue (x ≤ y)) { apply @leq_trans x (s x) y c h; };
  have f:π (istrue (y ≤ x)) { apply @leq_trans y (s y) x d i; };
  have g:π (istrue (x ≤ y) ∧ istrue (y ≤ x)) { apply ∧ᵢ e f; }; 
  apply ∧ₑ₁ (eqn_leq x y) g;
end;

opaque symbol leq_total x y : π (istrue (x ≤ y) ∨ istrue (y ≤ x)) ≔
begin
  induction
  { assume y; simplify; apply ∨ᵢ₁; apply top; }
  { assume x h; induction
    { simplify; apply ∨ᵢ₂; apply top; }
    { assume y i; simplify; apply h y; }
  }
end;

opaque symbol lt0n n : π (istrue (n > 0) ⇔ (n ≠ 0)) ≔
begin
  assume n; apply ∧ᵢ {
    generalize n; induction
    { assume h i; apply h; }
    { assume n h i j; apply s≠0 j;}
  } {
    generalize n; induction
    { assume h; apply h (eq_refl 0); }
    { assume n h i; apply top; }
  };
end;

opaque symbol leq_eqVlt m n : π (istrue (m ≤ n) ⇔ (m = n) ∨ istrue (m < n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { induction
      { assume h; apply ∨ᵢ₁ (eq_refl 0) }
      { assume n h i; apply ∨ᵢ₂ top }
    }
    { assume m h; induction
      { assume i; apply ∨ᵢ₂ i }
      { assume n i j; apply ∨ₑ (h n j)
        { assume e; apply ∨ᵢ₁; rewrite e; reflexivity }
        { assume e; apply ∨ᵢ₂; apply e }
      }
    }
  } {
    assume h; apply ∨ₑ h {
      assume i; apply eq_leq m n i 
    } {
      assume i; apply ltnW m n i
    }
  }
end;

opaque symbol ltn_neqAle m n : π (istrue (m < n) ⇔ istrue (m ≤ n) ∧ (m ≠ n)) ≔
begin
abort;

opaque symbol leq_add0 m n :
  π (istrue (0 ≤ m)) → π (istrue (0 ≤ n)) → π (istrue (0 ≤ m + n)) ≔
begin
  assume m n h i; apply leq0n (m + n);
end;

opaque symbol leq_add2l p m n : π (istrue (p + m ≤ p + n) ⇔ istrue (m ≤ n)) ≔
begin
  assume p m n; apply ∧ᵢ {
    //FIXME: generalize p fails
    generalize m; generalize p; induction
    { assume m n h; apply h; }
    { assume p h m n i; apply h m n i; }
  } {
    generalize m; generalize p; induction
    { assume m n h; apply h; }
    { assume p h m n i; apply h m n i; }
  }; 
end;

opaque symbol ltn_add2l p m n : π (istrue (p + m < p + n) ⇔ istrue (m < n)) ≔
begin
  assume p m n; simplify; rewrite left addnS; refine leq_add2l p (s m) n;
end;

opaque symbol leq_add2r p m n : π (istrue (m + p ≤ n + p) ⇔ istrue (m ≤ n)) ≔
begin
  assume p m n; rewrite addnC m p; rewrite addnC n p; refine leq_add2l p m n; 
end;

opaque symbol ltn_add2r p m n : π (istrue (m + p < n + p) ⇔ istrue (m < n)) ≔
begin
  assume p m n; rewrite addnC m p; rewrite addnC n p; refine ltn_add2l p m n; 
end;

opaque symbol leq_addl m n : π (istrue (n ≤ m + n)) ≔
begin
  assume m; induction
  { apply top; }
  { assume n h; apply h; }
end;

opaque symbol leq_addr m n : π (istrue (n ≤ n + m)) ≔
begin
  assume m n; rewrite addnC n m; apply leq_addl m n;
end;

opaque symbol leq_subr m n : π (istrue (n - m ≤ n)) ≔
begin
  induction
  { assume n; apply ≤_refl n; }
  { assume m h; induction
    { apply top; }
    { assume n i; simplify; 
      have t: π (istrue (n ≤ s n)) { apply leqnSn n };
      apply @leq_trans (n - m) n (s n) (h n) t;
    }
  }
end;

opaque symbol subn_eq0 m n : π ((m - n = 0) ⇔ istrue (m ≤ n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n h; apply top; }
    { assume m h; induction
      { assume i; apply s≠0 i; }
      { assume n i j; apply h n j; }
    }
  } {
    generalize m; induction
    { assume n h; apply eq_refl 0; }
    { assume m h; induction
      { assume i; apply ⊥ₑ i; }
      { assume n i j; apply h n j; }
    }
  };
end;

opaque symbol ltn_addl m n p : π (istrue (m < n)) → π (istrue (m < p + n)) ≔
begin
  assume m n; induction
  { assume h; apply h; }
  { assume p h i; refine @leq_trans m (s m) (p + n) (leqnSn m) (h i); }
end;

opaque symbol ltn_addr m n p : π (istrue (m < n)) → π (istrue (m < n + p)) ≔
begin
  assume m n p h; rewrite addnC n p; apply ltn_addl m n p; apply h;
end; 

opaque symbol addn_gt0 m n :
  π (istrue (0 < m + n) ⇔ istrue (0 < m) ∨ istrue (0 < n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n i; apply ∨ᵢ₂ i; }
    { assume m h n i; apply ∨ᵢ₁; apply ltn0Sn m; }
  } {
    assume h; apply ∨ₑ h {
      assume i; apply ltn_addr 0 m n i;
    } {
      assume i; apply ltn_addl 0 n m i;
    };
  };
end;

opaque symbol subn_gt0 m n : π (istrue (0 < n - m) ⇔ istrue (m < n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n h; apply h; }
    { assume m h; induction
      { assume i; apply i; }
      { assume n i; rewrite subSS; assume j; 
        have t: π (istrue (m < n)) { apply h n j; };
        have u: π (istrue (m + 1 < n + 1)) { refine ∧ₑ₂ (ltn_add2r 1 m n) t; };
        rewrite left addn1 m; rewrite left addn1 n; apply u;
      }
    }
  } {
    generalize m; induction
    { assume n h; apply h; }
    { assume m h; induction
      { assume i; apply i; }
      { assume n i j; rewrite subSS; apply h n;
        refine ∧ₑ₁ (ltn_add2r 1 m n) j;
      }
    }
  };
end;

opaque symbol leq_add m1 m2 n1 n2 :
  π (istrue (m1 ≤ n1)) → π (istrue (m2 ≤ n2)) → π (istrue (m1 + m2 ≤ n1 + n2)) ≔
begin
  assume m1 m2 n1 n2 h i;
  have a: π (istrue (m1 + m2 ≤ m1 + n2)) { apply ∧ₑ₂ (leq_add2l m1 m2 n2) i; };
  have b: π (istrue (m1 + n2 ≤ n1 + n2)) { refine ∧ₑ₂ (leq_add2r n2 m1 n1) h; };
  refine @leq_trans (m1 + m2) (m1 + n2) (n1 + n2) a b;
end;

opaque symbol leq_subLR m n p : π (istrue (m - n ≤ p) ⇔ istrue (m ≤ n + p)) ≔
begin
  assume m n p; apply ∧ᵢ
  { assume h;
    have t: π (((m - (n + p)) = 0)) → π (istrue (m ≤ (n + p)))
      { apply ∧ₑ₁ (subn_eq0 m (n + p)); };
    apply t; rewrite subnDA; apply ∧ₑ₂ (subn_eq0 (m - n) p) h;
  }
  { assume h; 
    have t: π (((m - n) - p) = 0) → π (istrue ((m - n) ≤ p))
      { apply ∧ₑ₁ (subn_eq0 (m - n) p); };
    apply t; rewrite left subnDA; apply ∧ₑ₂ (subn_eq0 m (n + p)) h;
  };
end;

opaque symbol subnKC m n : π (istrue (m ≤ n)) → π (m + (n - m) = n) ≔
begin
  induction
  { assume n h; apply eq_refl n; }
  { assume m h; induction
    { assume i; apply ⊥ₑ i; }
    { assume n i j; apply feq s; apply h; apply j; }
  }
end;

opaque symbol addnBn m n : π (m + (n - m) = m - n + n) ≔
begin
  induction
  { assume n; apply eq_refl n; }
  { assume m h; induction
    { apply eq_refl (s m); }
    { assume n i; simplify; apply feq s; apply h n; }
  }
end;

opaque symbol subnK m n : π (istrue (m ≤ n)) → π ((n - m) + m = n) ≔
begin
  assume m n h; rewrite addnC; apply subnKC m n h;
end;

opaque symbol subSn n p : π (istrue (p ≤ n)) → π (s n - p = s (n - p)) ≔
begin
  induction
  { assume p h; simplify;
    have t: π (p = 0) { apply ≤0 p h; };
    rewrite t; reflexivity;
  } {
    assume n h; induction
    { assume i; reflexivity; }
    { assume p i j; apply h p j }
  }
end;

opaque symbol addnBA m n p : π (istrue (p ≤ n))  → π (m + (n - p) = m + n - p) ≔
begin
  induction
  { assume n p h; reflexivity; }
  { assume m h n p i; simplify; rewrite left addnS m (n - p);
    rewrite left addnS m n; rewrite left h (s n) p (leqW p n i);
    rewrite subSn n p i; reflexivity; 
  }
end;

opaque symbol addnBAC m n p : π (istrue (n ≤ m)) → π (m - n + p = m + p - n) ≔
begin
  assume m n p h;
  rewrite addnC; rewrite addnBA p m n h; rewrite addnC; reflexivity;
end;

opaque symbol leq_sub2r m n p : π (istrue (m ≤ n)) → π (istrue (m - p ≤ n - p)) ≔
begin
  assume m n p h; apply ∧ₑ₂ (leq_subLR m p (n - p)) _;
  apply ∨ₑ (leq_total p n) {
    assume i; rewrite subnKC p n i; apply h;
  } {
    assume i;
    have t: π(n - p = 0) { apply ∧ₑ₂ (subn_eq0 n p) i };
    rewrite t; simplify; apply @leq_trans m n p h i;
  };
end;

opaque symbol leq_sub2l m n p : π (istrue (m ≤ n)) → π (istrue (p - n ≤ p - m)) ≔
begin
  assume m n p h; apply ∧ₑ₂ (leq_subLR p n (p - m)) _;
  apply ∨ₑ (leq_total p m) {
    assume i;
    have t:π (p - m = 0) { apply (∧ₑ₂ (subn_eq0 p m) i) };
    rewrite t; simplify; apply @leq_trans p m n i h;
  } {
    assume i; apply ∧ₑ₁ (leq_add2r m p (n + (p - m))) _;
    rewrite addnA; rewrite subnK m p i; rewrite addnC n p;
    apply ∧ₑ₂ (leq_add2l p m n) h;
  };
end;

opaque symbol leq_sub m1 m2 n1 n2 :
  π (istrue (m1 ≤ m2)) → π (istrue (n2 ≤ n1)) → π (istrue (m1 - n1 ≤ m2 - n2)) ≔
begin
  assume m1 m2 n1 n2 h i;
  have t:π (istrue (m1 - n1 ≤ m2 - n1)) { apply leq_sub2r m1 m2 n1 h; };
  have u:π (istrue (m2 - n1 ≤ m2 - n2)) { apply leq_sub2l n2 n1 m2 i; };
  apply @leq_trans (m1 - n1) (m2 - n1) (m2 - n2) t u;
end;

// max

symbol max: ℕ → ℕ → ℕ;

rule max 0 $x ↪ $x
with max $x 0 ↪ $x
with max (s $x) (s $y) ↪ s (max $x $y);

opaque symbol maxnC x y : π (max x y = max y x) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; simplify; rewrite h; reflexivity }
  }
end;

opaque symbol maxnA x y z : π (max (max x y) z = max x (max y z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; rewrite h; reflexivity }
    }
  }
end;

opaque symbol maxnAC x y z : π (max (max x y) z = max (max x z) y) ≔
begin
  assume x y z; rewrite maxnA; rewrite maxnC y z; rewrite left maxnA;
  reflexivity;
end;

opaque symbol maxnCA x y z : π (max x (max y z) = max y (max x z)) ≔
begin
  assume x y z; rewrite left maxnA; rewrite maxnC x y; rewrite maxnA;
  reflexivity; 
end;

opaque symbol maxnACA x y z t: π (max (max x y) (max z t) = max (max x z) (max y t)) ≔
begin
  assume x y z t; rewrite maxnA; rewrite maxnC y (max z t); rewrite maxnA;
  rewrite left maxnA x z; rewrite maxnC t y; reflexivity;
end;

opaque symbol addn_maxl x y z: π ((max y z) + x = max (y + x) (z + x)) ≔
begin
  induction
  { reflexivity; }
  { assume x h y z; simplify; apply feq s; rewrite h; reflexivity;}
end;

opaque symbol addn_maxr x y z : π (x + (max y z) = max (x + y) (x + z)) ≔
begin
  induction
  { reflexivity }
  { assume x h y z; simplify; apply feq s; rewrite h; reflexivity }
end;

opaque symbol subn_maxl x y z: π ( (max x y) - z = max (x - z) (y - z) ) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; simplify; apply h y z; }
    }
  }
end;

opaque symbol maxnE m n : π (max m n = m + (n - m)) ≔
begin
  induction
  { assume n; reflexivity; }
  { assume m h; induction
    { simplify;  reflexivity; }
    { assume n i; simplify; rewrite h; reflexivity; }
  }
end;

opaque symbol maxnn x : π (max x x = x) ≔
begin
  induction
  { reflexivity; }
  { assume x h; simplify; rewrite h; reflexivity; }
end;

rule max $x $x ↪ $x;

opaque symbol leq_maxl m n : π (istrue (m ≤ max m n)) ≔
begin
  induction
  { assume n; apply top; }
  { assume m h; induction
    { simplify; apply ≤_refl m; }
    { assume n i; simplify; apply h n; }
  }
end;

opaque symbol leq_maxr m n : π (istrue (n ≤ max m n)) ≔
begin
  assume m n; rewrite maxnC m n; apply leq_maxl n m;
end;

opaque symbol gtn_max m n1 n2 :
  π (istrue (m > max n1 n2) ⇔ istrue (m > n1) ∧ istrue (m > n2)) ≔
begin
abort;

opaque symbol geq_max m n1 n2 :
  π (istrue (m ≥ max n1 n2) ⇔ istrue (m ≥ n1) ∧ istrue (m ≥ n2)) ≔
begin
abort;

opaque symbol ltn_predK m n : π (istrue (m < n)) → π (s (p n) = n) ≔
begin
  assume m; induction
  { assume h; refine ⊥ₑ h; }
  { assume n h i; reflexivity; }
end;

opaque symbol prednK n : π (istrue (0 < n)) → π (s (p n) = n) ≔
begin
  refine ltn_predK 0; 
end;

opaque symbol leq_pmull m n : π (istrue (n > 0)) → π (istrue (m ≤ n * m)) ≔
begin
  assume m n h; 
  have t: π (s (p n) = n) { apply prednK n h; };
  rewrite left t; simplify; apply leq_addr (p n * m) m; 
end;

opaque symbol leq_pmulr m n : π (istrue (n > 0)) → π (istrue (m ≤ m * n)) ≔
begin
  assume m n h; rewrite mulnC; apply leq_pmull m n h; 
end; 

opaque symbol leq_mul2l m n1 n2 :
  π (istrue (m * n1 ≤ m * n2) ⇔ (m = 0) ∨ istrue (n1 ≤ n2)) ≔
begin
  assume m n1 n2;
  apply ∧ᵢ { 
    assume h;
    have t:π (m * (n1 - n2) = 0) {
      rewrite mulnBr; apply ∧ₑ₂ (subn_eq0 (m * n1) (m * n2)) h;
    };
    have u: π (m = 0 ∨ n1 - n2 = 0) { apply ∧ₑ₁ (muln_eq0 m (n1 - n2)) t; };
    apply ∨ₑ u {
      assume i; refine ∨ᵢ₁ i; 
    } {
      assume i; apply ∨ᵢ₂; apply ∧ₑ₁ (subn_eq0 n1 n2) i; 
    }; 
  } { 
    assume h; apply ∧ₑ₁ (subn_eq0 (m * n1) (m * n2)) _; rewrite left mulnBr;
    apply ∨ₑ h { 
      assume i; rewrite i; reflexivity; 
    } {
      assume i;
      have t:π (n1 - n2 = 0) { apply ∧ₑ₂ (subn_eq0 n1 n2) i; };
      rewrite t; reflexivity;
    };
  }
end;

opaque symbol leq_mul2r m n1 n2 :
  π (istrue (n1 * m ≤ n2 * m) ⇔ (m = 0) ∨ (istrue (n1 ≤ n2))) ≔
begin
  assume m n1 n2; rewrite mulnC n1 m; rewrite mulnC n2 m;
  refine leq_mul2l m n1 n2; 
end;

opaque symbol leq_mul m1 m2 n1 n2 :
  π (istrue (m1 ≤ n1)) → π (istrue (m2 ≤ n2)) → π (istrue (m1 * m2 ≤ n1 * n2)) ≔
begin
  assume m1 m2 n1 n2 h1 h2;
  have t1:π ((m2 = 0) ∨ istrue (m1 ≤ n1)) { apply ∨ᵢ₂ h1; };
  have t2:π ((n1 = 0) ∨ istrue (m2 ≤ n2)) { apply ∨ᵢ₂ h2; };
  have u1:π (istrue (m1 * m2 ≤ n1 * m2)) { apply ∧ₑ₂ (leq_mul2r m2 m1 n1) t1 };
  have u2:π (istrue (n1 * m2 ≤ n1 * n2)) { apply ∧ₑ₂ (leq_mul2l n1 m2 n2) t2 }; 
  apply @leq_trans (m1 * m2) (n1 * m2) (n1 * n2) u1 u2;
end;

opaque symbol eqn_mul2l m n1 n2 : π (m * n1 = m * n2 ⇔ (m = 0) ∨ (n1 = n2)) ≔
begin
  assume m n1 n2;
  apply ∧ᵢ {
    assume h;
    have t:π (istrue (m * n1 ≤ m * n2) ∧ istrue (m * n2 ≤ m * n1))
      { apply ∧ₑ₂ (eqn_leq (m * n1) (m * n2)) h; };
    have t1:π (istrue (m * n1 ≤ m * n2)) { apply ∧ₑ₁ t; };
    have t2:π (istrue (m * n2 ≤ m * n1)) { apply ∧ₑ₂  t; };
    have u1: π ((m = 0) ∨ istrue (n1 ≤ n2)) { apply ∧ₑ₁(leq_mul2l m n1 n2) t1 };
    have u2: π ((m = 0) ∨ istrue (n2 ≤ n1)) { apply ∧ₑ₁(leq_mul2l m n2 n1) t2 };
    apply ∨ₑ u1 {
      assume i; apply ∨ᵢ₁ i;
    } {
      assume i; 
      apply ∨ₑ u2 {
        assume j; apply ∨ᵢ₁ j;
      } {
        assume j; apply ∨ᵢ₂ _;
        apply ∧ₑ₁ (eqn_leq n1 n2) (∧ᵢ i j);
      };
    };
  } {
    assume h;
    apply ∨ₑ h {
      assume i; rewrite i; reflexivity;
    } {
      assume i; rewrite i; reflexivity;
    };
  };
end;

opaque symbol eqn_mul2r m n1 n2 : π ((n1 * m = n2 * m) ⇔ (m = 0) ∨ (n1 = n2)) ≔
begin
  assume m n1 n2; rewrite mulnC n1 m; rewrite mulnC n2 m;
  refine eqn_mul2l m n1 n2;
end;

opaque symbol leq_pmul2l m n1 n2 :
  π (istrue (0 < m)) → π (istrue (m * n1 ≤ m * n2) ⇔ istrue (n1 ≤ n2)) ≔
begin
  assume m n1 n2 h;
  apply ∧ᵢ {
    assume i;
    have t: π ((m = 0) ∨ istrue (n1 ≤ n2)) { apply ∧ₑ₁ (leq_mul2l m n1 n2) i; };
    apply ∨ₑ t {
      assume j;
      have u: π (istrue (0 < 0)) { rewrite left .[m in (istrue (_ < m))] j; apply h; };
      refine ⊥ₑ u;
    } {
      assume j; apply j;
    };
  } {
    assume i; refine ∧ₑ₂ (leq_mul2l m n1 n2) _; refine ∨ᵢ₂ i; 
  };
end;

opaque symbol leq_pmul2r m n1 n2 :
  π (istrue (0 < m)) → π (istrue (n1 * m ≤ n2 * m) ⇔ istrue (n1 ≤ n2)) ≔
begin
  assume m n1 n2 h; rewrite mulnC n1 m; rewrite mulnC n2 m;
  refine leq_pmul2l m n1 n2 h;
end;

opaque symbol ltn0_neq0 m : π (istrue (0 < m) ⇔ m ≠ 0) ≔
begin
  assume m; apply ∧ᵢ {
    generalize m; induction
    { assume h i; apply h; }
    { assume m h i j; apply s≠0 j;}
  } {
    generalize m; induction
    { assume h; apply h (eq_refl 0); }
    { assume m h i; apply top; }
  };
end;

opaque symbol disj0 m : π (m = 0 ∨ m ≠ 0) ≔
begin
  induction
  { apply ∨ᵢ₁ (eq_refl 0); }
  { assume m h; apply ∨ᵢ₂; assume i; apply s≠0 i; }
end;

opaque symbol eqn_pmul2l m n1 n2 :
  π (istrue (0 < m)) → π (m * n1 = m * n2 ⇔ n1 = n2) ≔
begin
  assume m n1 n2 h;
  apply ∧ᵢ {
    assume i1;
    have i2: π (m * n2 = m * n1) { symmetry; apply i1; };
    have v1: π (istrue (m * n1 ≤ m * n2)) { apply eq_leq _ _ i1; };
    have v2: π (istrue (m * n2 ≤ m * n1)) { apply eq_leq _ _ i2; };
    have w1: π (istrue (n1 ≤ n2)) { apply ∧ₑ₁ (leq_pmul2l m n1 n2 h) v1 };
    have w2: π (istrue (n2 ≤ n1)) { apply ∧ₑ₁ (leq_pmul2l m n2 n1 h) v2 };
    apply ∧ₑ₁ (eqn_leq n1 n2) (∧ᵢ w1 w2);
  } {
    assume i;
    have t:π (m = 0 ∨ n1 = n2) { apply ∨ᵢ₂ i; };
    apply ∧ₑ₂ (eqn_mul2l m n1 n2) t;
  };
end;

opaque symbol eqn_pmul2r m n1 n2 :
  π (istrue (0 < m)) → π (n1 * m = n2 * m ⇔ n1 = n2) ≔
begin
  assume m n1 n2 h; rewrite mulnC n1 m; rewrite mulnC n2 m;
  apply eqn_pmul2l m n1 n2 h; 
end;

// min

symbol min : ℕ → ℕ → ℕ;

rule min 0 _ ↪ 0
with min _ 0 ↪ 0
with min (s $x) (s $y) ↪ s (min $x $y);

opaque symbol minnC x y : π (min x y = min y x) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; simplify; rewrite h; reflexivity; }
  }
end;

opaque symbol minnA x y z : π (min (min x y) z = min x (min y z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; rewrite h; reflexivity;}
    }
  }
end;

opaque symbol minnAC x y z : π (min (min x y) z = min (min x z) y) ≔
begin
  assume x y z; rewrite minnA; rewrite minnC y z; rewrite left minnA;
  reflexivity;
end;

opaque symbol minnCA x y z : π (min x (min y z) = min y (min x z)) ≔
begin
  assume x y z; rewrite left minnA; rewrite minnC x y; rewrite minnA;
  reflexivity; 
end;

opaque symbol minnACA x y z t :
  π (min (min x y) (min z t) = min (min x z) (min y t)) ≔
begin
  assume x y z t; rewrite minnA; rewrite minnC y (min z t); rewrite minnA;
  rewrite left minnA x z; rewrite minnC t y; reflexivity;
end;

opaque symbol addn_minl x y z: π ((min y z) + x = min (y + x) (z + x)) ≔
begin
  induction
  { reflexivity; }
  { assume x h y z; simplify; apply feq s; rewrite h; reflexivity;}
end;

opaque symbol addn_minr x y z: π (x + (min y z) = min (x + y) (x + z)) ≔
begin
  induction
  { reflexivity; }
  { assume x h y z; simplify; apply feq s; rewrite h; reflexivity;}
end;

opaque symbol subn_minl x y z: π ((min x y) - z = min (x - z) (y - z)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; simplify; apply h y z; }
    }
  }
end;

opaque symbol minnE m n : π (min m n = m - (m - n)) ≔
begin
  induction
  { reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; simplify; rewrite h; }
  }
abort;

opaque symbol minnn x : π (min x x = x) ≔
begin
  induction
  { reflexivity;}
  { assume x h; simplify; rewrite h; reflexivity; }
end;

rule min $x $x ↪ $x;

opaque symbol geq_minl m n : π (istrue (min m n ≤ m)) ≔
begin
  induction
  { assume n; apply top; }
  { assume m h; induction
    { apply top; }
    { assume n i; simplify; apply h n; }
  }
end;

opaque symbol geq_minr m n : π (istrue (min m n ≤ n)) ≔
begin
  assume m n; rewrite minnC; apply geq_minl n m;
end;

// proofs on max and min

opaque symbol addn_min_max m n : π (min m n + max m n = m + n) ≔
begin
  induction
  { assume m; reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; simplify; rewrite h n; reflexivity; }
  }
end;

opaque symbol maxnK m n : π (min (max m n) m = m) ≔
begin
  induction
  { assume n; reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; simplify; rewrite h n; reflexivity; }
  }
end;

opaque symbol maxKn m n : π (min n (max m n) = n) ≔
begin
  induction
  { assume n; reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; simplify; rewrite h n; reflexivity; }
  }
end;

opaque symbol minnK m n : π (max (min m n) m = m) ≔
begin
  induction
  { assume n; reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; simplify; rewrite h n; reflexivity; }
  }
end;

opaque symbol minKn m n : π (max n (min m n) = n) ≔
begin
  induction
  { assume n; reflexivity; }
  { assume m h; induction
    { reflexivity; }
    { assume n i; simplify; rewrite h n; reflexivity; }
  }
end;

opaque symbol maxn_minl x y z : π (max x (min y z) = min (max x y) (max x z)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; simplify; rewrite minnC; rewrite maxnK (s x) z; reflexivity; }
    { assume y i; induction
      { simplify; rewrite maxnK x y; reflexivity; }
      { assume z j; simplify; rewrite h; reflexivity; }
    }
  }
end;

opaque symbol maxn_minr x y z : π (max (min y z) x = min (max y x) (max z x)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; simplify; rewrite maxKn z (s x); reflexivity; }
    { assume y i; induction
      { simplify; rewrite maxnC; rewrite maxnK x y; reflexivity; }
      { assume z j; simplify; rewrite h; reflexivity; }
    }
  }
end;

opaque symbol minn_maxl x y z : π (min x (max y z) = max (min x y) (min x z)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; simplify; rewrite h; reflexivity; }
    }
  }
end;

opaque symbol minn_maxr x y z : π (min (max y z) x = max (min y x) (min z x)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; simplify; rewrite h; reflexivity; }
    }
  }
end;

opaque symbol maxnMr x y z : π ((max y z) * x = max (y * x) (z * x)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; rewrite left addn1 y; rewrite left addn1 z; 
        rewrite left addn_maxl 1 y z; symmetry; 
        rewrite mulnDl y 1 (s x); rewrite mulnDl z 1 (s x); 
        rewrite left addn_maxl (1 * s x) (y * s x) (z * s x); rewrite left i; 
        symmetry; rewrite mulnDl (max y z) 1 (s x); reflexivity;
      }
    }
  }
end;

opaque symbol maxnMl x y z : π (x * (max y z) = max (x * y) (x * z)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; rewrite left addn1 y; rewrite left addn1 z; 
        rewrite left addn_maxl 1 y z; symmetry; 
        rewrite mulnDr y 1 (s x); rewrite mulnDr z 1 (s x); 
        rewrite left addn_maxl (s x * 1) (s x * y) (s x * z); rewrite left i; 
        symmetry; rewrite mulnDr (max y z) 1 (s x); reflexivity;
      }
    }
  }
end;

opaque symbol minnMr x y z : π ((min y z) * x = min (y * x) (z * x)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; rewrite left addn1 y; rewrite left addn1 z; 
        rewrite left addn_minl 1 y z; symmetry; 
        rewrite mulnDl y 1 (s x); rewrite mulnDl z 1 (s x); 
        rewrite left addn_minl (1 * s x) (y * s x) (z * s x); rewrite left i; 
        symmetry; rewrite mulnDl (min y z) 1 (s x); reflexivity;
      }
    }
  }
end;

opaque symbol minnMl x y z : π (x * (min y z) = min (x * y) (x * z)) ≔
begin
  induction
  { assume y z; reflexivity; }
  { assume x h; induction
    { assume z; reflexivity; }
    { assume y i; induction
      { reflexivity; }
      { assume z j; rewrite left addn1 y; rewrite left addn1 z; 
        rewrite left addn_minl 1 y z; symmetry; 
        rewrite mulnDr y 1 (s x); rewrite mulnDr z 1 (s x); 
        rewrite left addn_minl (s x * 1) (s x * y) (s x * z); rewrite left i; 
        symmetry; rewrite mulnDr (min y z) 1 (s x); reflexivity;
      }
    }
  }
end;

// exponentiation

symbol ^ : ℕ → ℕ → ℕ; notation ^ infix left 40;

rule _ ^ 0 ↪ 1
with $n ^ s $m ↪ $n * $n ^ $m;

opaque symbol expn0 m : π (m ^ 0 = 1) ≔
begin
  assume m; reflexivity;
end;

opaque symbol expn m : π (m ^ 1 = m) ≔
begin
  assume m; simplify; rewrite mulnS; reflexivity;
end;

opaque symbol expnS a n : π (a ^ s n = a * a ^ n ) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h; reflexivity;}
end;

opaque symbol expnSr a n : π (a ^ s n = a ^ n * a) ≔
begin
  assume a n; rewrite expnS a n; rewrite mulnC; reflexivity;
end;

opaque symbol exp0n n : π (istrue (0 < n)) → π (0 ^ n = 0) ≔
begin
  induction
  { assume h; refine ⊥ₑ h;}
  { assume n h i; reflexivity; }
end;

opaque symbol exp1n n : π (1 ^ n = 1) ≔
begin
  induction
  { reflexivity; }
  { assume n h; simplify; rewrite h; reflexivity; }
end;

opaque symbol expnD a m n: π (a ^ (m + n) = a ^ m * a ^ n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume m h n; simplify; rewrite h n; rewrite mulnA; reflexivity; }
end;

opaque symbol expnMn m1 m2 n : π ((m1 * m2) ^ n = m1 ^ n * m2 ^ n) ≔
begin
  assume m1 m2; induction
  { reflexivity; }
  { assume n h;  simplify; rewrite h; rewrite mulnA; rewrite mulnA;
    rewrite left mulnA (m1 ^ n) m2; rewrite mulnC (m1 ^ n) m2;
    rewrite mulnA m2 (m1 ^ n); reflexivity;
  }
end;

opaque symbol expnM m n1 n2 : π (m ^ (n1 * n2) = (m ^ n1) ^ n2) ≔
begin
  assume m; induction
  { assume n2; simplify; rewrite exp1n; reflexivity; }
  { assume n1 h n2; simplify; rewrite expnD; rewrite h n2;
    rewrite left expnMn; reflexivity; }
end;

opaque symbol expnAC m n1 n2 : π ((m ^ n1) ^ n2 = (m ^ n2) ^ n1) ≔
begin
  assume m n1 n2; rewrite left expnM; rewrite mulnC; rewrite expnM;
  reflexivity; 
end;

opaque symbol expn_gt0 m n :
  π ((istrue (0 < m ^ n)) ⇔ istrue (0 < m) ∨ (n = 0)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize n; induction
    { assume h; apply ∨ᵢ₂ (eq_refl 0); }
    { assume n h i;
      have t: π (istrue (0 < m ^ n)) { };
    }
  } {
  };
abort;

opaque symbol ltn_expl m n : π (istrue (1 < m)) → π (istrue (n < m ^ n)) ≔
begin
  assume m; induction
  { assume h; apply top; }
  { assume n h i; 
    have t: π (istrue (n < (m ^ n))) { apply h i; };
    rewrite expnS; 
  }
abort;

// factorial

symbol ! : ℕ → ℕ; notation ! postfix 40;

rule 0 ! ↪ 1
with (s $n) ! ↪ (s $n) * $n !;

opaque symbol fact0 : π (0 ! = 1) ≔
begin
  reflexivity;
end;

opaque symbol factS n : π ((s n) ! = s n * n !) ≔
begin
  reflexivity; 
end;

opaque symbol fact_gt0 n : π (istrue (n ! > 0)) ≔
begin
  induction
  { apply top; }
  { assume n h; rewrite factS n; rewrite mulSnr n (n !);
    apply ltn_addl 0 (n !) (n * n !); apply h; }
end;

opaque symbol fact_gt1 n : π (istrue (n ! ≥ 1)) ≔
begin
  refine fact_gt0;
end;

opaque symbol fact_geq n : π (istrue (n ≤ n !)) ≔
begin
  induction
  { apply top; }
  { assume n h; rewrite factS n; apply leq_pmulr (s n) (n !) (fact_gt0 n); }
end;
