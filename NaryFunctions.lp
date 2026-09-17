// Implementation of N-ary functions and relations based on Guillaume Allais,
// "Generic Level Polymorphic N-ary Functions" (TyDe 2019).
// This API provides n-ary functions which automatically reconstruct the representation of their inputs' types by unification.
// It helps to define fully level polymorphic n-ary versions of congruence, substitution and the combinators for indexed families,
// that are used by programs such as SMT solvers. Lemmas provided in the rest of the library such as `Eq.lp` are implemented for
// fixed arities, and the implementation here aims to provide similar lemmas for N-ary Combinators.

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.HOL Stdlib.Nat Stdlib.Eq Stdlib.Impred;

inductive Sets : ℕ → TYPE ≔
| unit : Sets 0
| ▹ : Π [n : ℕ], Set → Sets n → Sets (n +1);

notation ▹ infix right 10;

symbol sets (n : ℕ) : Set;
rule τ (sets $n) ↪ Sets $n;

// Type transformer x1 ▹ x2 ▹ .. into  x1 ⤳ x2 ⤳ ..
symbol arrows [n] : Sets n → Set → Set;
rule arrows unit $b ↪ $b
with arrows ($t ▹ $ts) $b ↪ $t ⤳ arrows $ts $b;

injective symbol Arrow [n] (dom : Sets n) (cod : Set) : TYPE ≔ τ (arrows dom cod);

assert ⊢ Arrow (o ▹ o ▹ unit) o ≡ Prop → Prop → Prop;
assert ⊢ (∧) : Arrow (o ▹ o ▹ unit) o;

// Helper type constructor to just create an arrow of `n`-times the type `t`.
// Ex: sets_ident 3 nat ≡ nat ▹ nat ▹ nat ▹ unit
symbol sets_ident n (t : Set) : Sets n;
rule sets_ident 0 _ ↪ unit
with sets_ident ($n +1) $t ↪ $t ▹ sets_ident $n $t;

// Type of the `n`-ary functions on `a`.
// Ex: ArrowI 2 nat ≡ nat ⤳ nat ⤳ nat
symbol ArrowI n (a : Set) ≔ Arrow (sets_ident n a) a;


// Lift a unary operation (τ a → τ b) to n-ary functions.
symbol lift [a b : Set] n [dom : Sets n] : (τ a → τ b) → Arrow dom a → Arrow dom b;
rule @lift _ _ _ unit $op $f ↪ $op $f
with @lift _ _ _ ($t ▹ $ts) $op $f ↪ λ x : τ $t, @lift _ _ _ $ts $op ($f x);

// Lift a binary operation to two n-ary functions with the same domain
symbol lift2 [a b c : Set] n [dom : Sets n] :
  (τ a → τ b → τ c) → Arrow dom a → Arrow dom b → Arrow dom c;
rule @lift2 _ _ _ _ unit $op $f $g ↪ $op $f $g
with @lift2 _ _ _ _ ($t ▹ $ts) $op $f $g ↪ λ x : τ $t, @lift2 _ _ _ _ $ts $op ($f x) ($g x);

// `composeₙ n g f` precomposes the (n+1)-th argument of g with f:
// composition with f, lifted over the first n arguments.
symbol composeₙ [i j b : Set] n [dom : Sets n] (g : Arrow dom (j ⤳ b)) (f : τ i → τ j)
  : Arrow dom (i ⤳ b) ≔ lift n (λ h, h ∘ f) g;

symbol ∧ₙ [n] [dom : Sets n] (p q : Arrow dom o) : Arrow dom o ≔ lift2 n (∧) p q;

symbol ∨ₙ [n] [dom : Sets n] (p q : Arrow dom o) : Arrow dom o ≔ lift2 n (∨) p q;

symbol ⇒ₙ [n] [dom : Sets n] (p q : Arrow dom o) : Arrow dom o ≔ lift2 n (⇒) p q;

symbol quantₙ (q : Π a : Set, (τ a → Prop) → Prop) [n] [ts : Sets n] : Arrow ts o → Prop;
rule @quantₙ _ _ unit $p ↪ $p
with @quantₙ $q _ ($t ▹ $ts) $p ↪ $q $t (λ x : τ $t, @quantₙ $q _ $ts ($p x));

symbol ∀ₙ n [ts : Sets n] (p : Arrow ts o) : Prop ≔ quantₙ @∀ p;
symbol ∃ₙ n [ts : Sets n] (p : Arrow ts o) : Prop ≔ quantₙ @∃ p;

// cong f g computes the statement
//   `∀ a₁, `∀ b₁, a₁ = b₁ ⇒ ... ⇒ `∀ aₙ, `∀ bₙ, aₙ = bₙ ⇒ f a₁ .. aₙ = g b₁ .. bₙ
symbol cong [n] [ts : Sets n] [r : Set] (f g : Arrow ts r) : Prop;
rule @cong _ unit _ $f $g ↪ $f = $g
with @cong _ ($t ▹ $ts) $r $f $g ↪
  `∀ x : τ $t, `∀ y : τ $t, x = y ⇒ @cong _ $ts $r ($f x) ($g y);

opaque symbol congₙ [d : Set] n [ts : Sets n] (f : Arrow ts d) : π (cong f f) ≔
begin
  assume d n;
  refine ind_Sets (λ n u, `∀ f, @cong n u d f f) _ _ n
  { reflexivity }
  { assume m t ts ih;
    assume f t1 t2 hrefl;
    rewrite hrefl;
    refine ih (f t2) }
end;

// subst p q computes the statement
//   `∀ a₁, `∀ b₁, a₁ = b₁ ⇒ ... ⇒ `∀ aₙ, `∀ bₙ, aₙ = bₙ ⇒ p a₁ .. aₙ ⇒ q b₁ .. bₙ
symbol subst [n] [ts : Sets n] (p q : Arrow ts o) : Prop;
rule @subst _ unit $p $q ↪ $p ⇒ $q
with @subst _ ($t ▹ $ts) $p $q ↪
  `∀ x : τ $t, `∀ y : τ $t, x = y ⇒ @subst _ $ts ($p x) ($q y);

opaque symbol substₙ n [ts : Sets n] (p : Arrow ts o) : π (subst p p) ≔
begin
  assume n;
  refine ind_Sets (λ n u, `∀ p, @subst n u p p) _ _ n
  { assume p h; refine h }
  { assume m t ts ih;
    assume p x y hxy;
    rewrite hxy;
    refine ih (p y) }
end;

symbol tl [n] : Sets (n +1) → Sets n;
rule tl (_ ▹ $ts) ↪ $ts;

// The definitions above do not depend on the following unification rules:
// they only let the `Sets` argument stay implicit at use sites such as
// `congₙ 2 (+)`, where the arity `n` is given but the domain is not.
// The rules of `arrows` match on the `Sets` argument, so `arrows ?ts ?b` is
// stuck when `?ts` is a metavariable: for `f : τ a → τ b → τ c` against
// `Arrow ?ts ?d`, the unifier faces `arrows 2 ?ts ?d ≡ a ⤳ b ⤳ c`. The rules
// below unfold it one step at a time, guided by `n`, which determines the
// constructor of `?ts`.
unif_rule @arrows ($n +1) $ts $b ≡ ($a ⤳ $c) ↪ [$ts ≡ @▹ $n $a _; @arrows $n (@tl $n $ts) $b ≡ $c];
unif_rule @arrows 0 $ts $b ≡ $c ↪ [$ts ≡ unit; $b ≡ $c];

// Examples

private symbol f1 : Arrow (o ▹ o ▹ o ▹ o ▹ unit) o;
private symbol f2 : ArrowI 4 o;

private opaque symbol ex_cong a b c d x y w z :
  π (a = x) → π (b = y) → π (c = w) → π (d = z) → π (f1 a b c d = f1 x y w z) ≔
begin
  assume a b c d x y w z heq1 heq2 heq3 heq4;
  refine congₙ 4 f1 _ _ heq1 _ _ heq2 _ _ heq3 _ _ heq4
end;

assert (x y : ℕ)
  ⊢ let u1 ≔ composeₙ 1 (+) (λ x, x +1) in
    u1 x y ≡ x + (y +1);

private opaque symbol testSubst (p : Arrow (nat ▹ nat ▹ unit) o) (a b x y : ℕ) :
  π (a = x) → π (b = y) → π (p a b) → π (p x y) ≔
begin assume p a b x y hax hby; refine substₙ 2 p _ _ hax _ _ hby end;
