/* N-ary functions and relations

following "Generic Level Polymorphic N-ary Functions" by Guillaume
Allais (TyDe 2019).

This API provides n-ary functions which automatically reconstruct the
representation of their inputs' types by unification. It helps to
define fully level polymorphic n-ary versions of congruence,
substitution and the combinators for indexed families, that are used
by programs such as SMT solvers. Lemmas provided in the rest of the
library such as `Eq.lp` are implemented for fixed arities, and the
implementation here aims to provide similar lemmas for N-ary
combinators. */

require open Stdlib.HOL Stdlib.Nat;

        // vectors of type codes
inductive VSet : ℕ → TYPE ≔
            | unit : VSet 0
                          | ▹ : Set → Π [n], VSet n → VSet (n +1); // \smalltriangleright

notation ▹ infix right 10;

// tail
symbol tl [n] : VSet (n +1) → VSet n;
rule tl (_ ▹ $ts) ↪ $ts;

// constant vector
injective symbol vcst n (t : Set) : VSet n;
rule vcst 0 _ ↪ unit
with vcst ($n +1) $t ↪ $t ▹ vcst $n $t;

// type code of n-ary functions: fun (a₁ ▹ … ▹ aₙ ▹ unit) b ≡ a₁ ⤳ … ⤳ aₙ ⤳ b
symbol fun [n] : VSet n → Set → Set;
rule fun unit $b ↪ $b
with fun ($t ▹ $ts) $b ↪ $t ⤳ fun $ts $b;

// fun is not injective, however (fun d) and (fun _ b) are both injective
// we can therefore safely add the following unification rules:
unif_rule fun $x $y ≡ fun $x $y' ↪ [$y ≡ $y'];
unif_rule fun $x $y ≡ fun $x' $y ↪ [$x ≡ $x'];
unif_rule fun $x $y ≡ $y ↪ [$x ≡ unit];

// type of n-ary functions: Fun 
symbol Fun [n] (dom : VSet n) cod ≔ τ (fun dom cod);

// type of n-ary endofunctions
injective symbol Endo n a ≔ Fun (vcst n a) a;

// lift (a₁ ▹ … ▹ aₙ ▹ unit) p f x₁ … xₙ ≡ p (f x₁ … xₙ) 
symbol lift [a b n] (d: VSet n): (τ a → τ b) → Fun d a → Fun d b;
rule lift unit $op $f ↪ $op $f
with lift (_ ▹ $ts) $op $f ↪ λ x, lift $ts $op ($f x);

// comp (a₁ ▹ … ▹ aₙ ▹ unit) g f x₁ … xₙ ≡ g x₁ … xₙ ∘ f
symbol comp [n] (d: VSet n) [j b] (g: Fun d (j ⤳ b)) [i] (f: τ i → τ j)
  : Fun d (i ⤳ b) ≔ lift d (λ h:_ → τ b, h ∘ f) g;

// lift2 (a₁ ▹ … ▹ aₙ ▹ unit) p f g x₁ … xₙ ≡ p (f x₁ … xₙ) (g x₁ … xₙ)
symbol lift2 [a b c n] (d: VSet n) :
  (τ a → τ b → τ c) → Fun d a → Fun d b → Fun d c;
rule lift2 unit $op $f $g ↪ $op $f $g
with lift2 (_ ▹ $ts) $op $f $g ↪ λ x, lift2 $ts $op ($f x) ($g x);

// cong (a₁ ▹ … ▹ aₙ ▹ unit) r f g ≡
// `∀ x₁,`∀ y₁, x₁ = y₁ ⇒ … ⇒ `∀ xₙ,`∀ yₙ, xₙ = yₙ ⇒ f x₁ … xₙ = g y₁ … yₙ
// we can declare r as implicit thanks to the unif_rule on Fun
symbol cong [n] (ts: VSet n) [r] (f g: Fun ts r): Prop;
rule cong unit $f $g ↪ $f = $g
with cong (_ ▹ $ts) $f $g ↪ `∀ x,`∀ y, x = y ⇒ cong $ts ($f x) ($g y);

// we can declare r as implicit thanks to the unif_rule on Fun
opaque symbol refl_cong [n] (ts: VSet n) [r] (f: Fun ts r): π(cong ts f f) ≔
begin
  have aux: Π r n (ts: VSet n) (f: Fun ts r), π(cong ts f f) {
    assume r n; refine ind_VSet (λ n ts, `∀ f, cong ts [r] f f) _ _ n
    { reflexivity }
    { assume t m ts ih f x y xy; rewrite xy; refine ih (f y) }
  };
  assume n ts r; refine aux r n ts
end;

require open Stdlib.Impred;

// subst (a₁ ▹ … ▹ aₙ ▹ unit) f g ≡
// `∀x₁:τa₁,`∀y₁, x₁ = y₁ ⇒ … ⇒ `∀xₙ:τaₙ,`∀yₙ, xₙ = yₙ ⇒ f x₁ … xₙ ⇒ g y₁ … yₙ
symbol subst [n] (ts: VSet n) (f g: Fun ts o): Prop;
rule subst unit $f $g ↪ $f ⇒ $g
with subst (_ ▹ $ts) $f $g ↪ `∀ x,`∀ y, x = y ⇒ subst $ts ($f x) ($g y);

opaque symbol refl_subst [n] (ts: VSet n) (p: Fun ts o): π(subst ts p p) ≔
begin
  assume n; refine ind_VSet (λ n ts, `∀ p, subst ts p p) _ _ n
  { assume p h; refine h }
  { assume t m ts ih p x y xy; rewrite xy; refine ih (p y) }
end;

// Lifted connectors

symbol ∧ₙ [n] [d: VSet n] ≔ lift2 d (∧);

symbol ∨ₙ [n] [d: VSet n] ≔ lift2 d (∨);

symbol ⇒ₙ [n] [d: VSet n] ≔ lift2 d (⇒);

// quantₙ Q (a₁ ▹ … ▹ aₙ ▹ unit) p ≡ `Q x₁, …, `Q xₙ, p x₁ … xₙ
symbol quantₙ (q: Π a, (τ a → Prop) → Prop) [n] (ts: VSet n): Fun ts o → Prop;
rule quantₙ _ unit $p ↪ $p
with quantₙ $q ($t ▹ $ts) $p ↪ $q $t (λ x, quantₙ $q $ts ($p x));

symbol ∀ₙ [n] ≔ @quantₙ @∀ n;
symbol ∃ₙ [n] ≔ @quantₙ @∃ n;

// Tests

private symbol f1 : Endo 4 o;

private opaque symbol ex_cong a b c d x y w z :
  π (a = x) → π (b = y) → π (c = w) → π (d = z) → π (f1 a b c d = f1 x y w z) ≔
begin
  assume a b c d x y w z heq1 heq2 heq3 heq4;
  refine refl_cong (o ▹ o ▹ o ▹ o ▹ unit) f1 _ _ heq1 _ _ heq2 _ _ heq3 _ _ heq4
end;

private opaque symbol ex_cong_param a b c d x y w z
  (g : Fun (o ▹ o ▹ o ▹ o ▹ unit) o) :
  π (a = x) → π (b = y) → π (c = w) → π (d = z) → π (g a b c d = g x y w z) ≔
begin
  assume a b c d x y w z g heq1 heq2 heq3 heq4;
  refine refl_cong (o ▹ o ▹ o ▹ o ▹ unit) g _ _ heq1 _ _ heq2 _ _ heq3 _ _ heq4
end;

private opaque symbol ex_cong_add (a b x y : ℕ) :
  π (a = x) → π (b = y) → π (a + b = x + y) ≔
begin
  assume a b x y h1 h2;
  refine refl_cong (nat ▹ nat ▹ unit) (+) _ _ h1 _ _ h2
end;

assert x y ⊢ let u ≔ comp (nat ▹ unit) (+) (+1) in u x y ≡ x + (y +1);

private opaque symbol testSubst (p: Fun (nat ▹ nat ▹ unit) o) a b x y:
  π (a = x) → π (b = y) → π (p a b) → π (p x y) ≔
begin
  assume p a b x y ax by;
  refine refl_subst (nat ▹ nat ▹ unit) p _ _ ax _ _ by
end;
