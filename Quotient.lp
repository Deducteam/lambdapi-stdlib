/*
   Encoding of the Quotient types interfaces following Jesper Cockx,
   [1] "Type Theory Unchained: Extending Agda with User-Defined Rewrite Rules" (TYPES 2019), §2.4.
   The code below try to follows as maximum the code presented in the paper but also adapt it to benefits some Lambdapi features.
*/
require open Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.PropExt Stdlib.Nat Stdlib.Prod;

// The type `Quot A R` written `A ⫽ R` consists of elements `proj x` where `x: A`
[a : Set] (R : τ a → τ a → Prop) inductive Quot : TYPE ≔
| proj : τ a → Quot R;

constant symbol ⫽ : Π (a : Set), (τ a → τ a → Prop) → Set; // \sslash
notation ⫽ infix 30;

rule τ (_ ⫽ $R) ↪ Quot $R;

// The `proj x` is equal to `proj y` if and only if `R x y` holds
constant symbol quot [a] [R : τ a → τ a → Prop] [x y : τ a] :
  π (R x y) → π (@proj a R x = @proj a R y);

symbol transport [a] (P : τ a → Set) [x y : τ a] : π (x = y) → τ (P x) → τ (P y);

rule @transport _ _ $x $x _ $z ↪ $z // correspond to transportR−refl in [1]
with @transport _ (λ _, _) _ _ _ $z ↪ $z; // transport P when P is constant only so typing is preserved.

// The elimination principle ⫽−elim allows us to define functions that extract an element of A from a given element of A ⫽ R,
//  provided a proof `quot∗` that the function respects the equality on A // R.
symbol ⫽-elim [a] [R : τ a → τ a → Prop] (P : τ (a ⫽ R) → Set)
  (proj* : Π x : τ a, τ (P (proj x)))
  (quot* : Π (x y : τ a) (r : π (R x y)), π (transport P (quot r) (proj* x) = proj* y))
  : Π q : τ (a ⫽ R), τ (P q);

// The computation rule below allows ⫽−elim to compute when it is applied to a proj x.
rule ⫽-elim _ $f _ (proj $x) ↪ $f $x;


// Non-dependent eliminator (i.e. recursor in HoTT)
symbol ⫽-rec [a] [R : τ a → τ a → Prop] [b] (f : τ a → τ b)
  (h : Π (x y : τ a), π (R x y) → π (f x = f y)) : τ (a ⫽ R) → τ b ≔
  ⫽-elim (λ _, b) f h;

assert (a : Set) (R : τ a → τ a → Prop) (b : Set) (f : τ a → τ b)
  (h : Π (x y : τ a), π (R x y) → π (f x = f y)) (x : τ a)
  ⊢ ⫽-rec f h (proj x) ≡ f x;

// Binary non-dependent eliminator
symbol ⫽-rec2 [a] [R : τ a → τ a → Prop] [c] (f : τ a → τ a → τ c)
  (refl : Π x : τ a, π (R x x))
  (h : Π (x x' y y' : τ a), π (R x x') → π (R y y') → π (f x y = f x' y'))
  : τ (a ⫽ R) → τ (a ⫽ R) → τ c ≔
  λ q1 q2,
    ⫽-rec (λ x, ⫽-rec (f x) (λ y y' s, h x x y y' (refl x) s) q2)
      (λ x x' r, ind_Quot a R (λ q, ⫽-rec (f x) (λ y y' s, h x x y y' (refl x) s) q
                                  = ⫽-rec (f x') (λ y y' s, h x' x' y y' (refl x') s) q)
                             (λ y, h x x' y y r (refl y)) q2) q1;

assert (a : Set) (R : τ a → τ a → Prop) (c : Set) (f : τ a → τ a → τ c)
  (refl : Π x : τ a, π (R x x))
  (h : Π (x x' y y' : τ a), π (R x x') → π (R y y') → π (f x y = f x' y'))
  (x y : τ a)
  ⊢ ⫽-rec2 f refl h (proj x) (proj y) ≡ f x y;


// `proj` identifies two elements only when they are related,
// so together with `quot` the quotient is exactly `a` modulo `R`:
//    R x y  ⇔  proj x = proj y
opaque symbol noconf [a] [R : τ a → τ a → Prop]
  (refl : Π x, π (R x x))
  (sym : Π x y, π (R x y) → π (R y x))
  (trans : Π x y z, π (R x y) → π (R y z) → π (R x z))
  (x y : τ a) : π (proj x = proj y) → π (R x y) ≔
begin
  assume a R refl sym trans x y h;
  have compat : Π (u v : τ a), π (R u v) → π (R x u = R x v)
  {
    assume u v r;
    refine propExt (R x u) (R x v) (λ k, trans x u v k r) (λ k, trans x v u k (sym u v r))
  };
  refine =⇒ (feq (⫽-rec (λ u, R x u) compat) h) (refl x)
end;

// Example from https://lawrencecpaulson.github.io/2022/03/30/Quotienting.html
// Let’s define the set of integers from pairs of natural numbers by quotienting.
// The required equivalence relation on such pairs is (a, b) ~ (c, d) ⟺ a + d = c + b
private symbol intrel (p q : τ (nat × nat)) : Prop ≔ (p ₁) + (q ₂) = (q ₁) + (p ₂);

private symbol int : Set ≔ (nat × nat) ⫽ intrel;

private symbol plus (p q : τ (nat × nat)) : τ (nat × nat) ≔ ((p ₁) + (q ₁)) ‚ ((p ₂) + (q ₂));

private opaque symbol plus_compat (p p' q q' : τ (nat × nat)) :
  π (intrel p p') → π (intrel q q') → π (intrel (plus p q) (plus p' q')) ≔
begin
  assume p p' q q' r s; simplify;
  rewrite addnACA (p ₁) (q ₁) (p' ₂) (q' ₂); rewrite r; rewrite s;
  rewrite addnACA (p' ₁) (q' ₁) (p ₂) (q ₂); reflexivity
end;

private symbol i+ : τ int → τ int → τ int ≔
  ⫽-rec2 (λ p q, proj (plus p q)) (λ p, eq_refl _)
    (λ p p' q q' r s, quot (plus_compat p p' q q' r s));

notation i+ infix left 20;

private opaque symbol i+_com (a b : τ int) : π (a i+ b = b i+ a) ≔
begin
  induction; assume p; induction; assume q;
  refine feq proj (feq2 (λ x y, x ‚ y) (addnC (p ₁) (q ₁)) (addnC (p ₂) (q ₂)))
end;