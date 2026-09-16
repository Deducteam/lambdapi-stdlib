// Implementation of N-ary functions and relations based on Guillaume Allais,
// "Generic Level Polymorphic N-ary Functions" (TyDe 2019).
// This API provides n-ary functions which automatically reconstruct the representation of their inputs' types by unification.
// It helps to define fully level polymorphic n-ary versions of congruence, substitution and the combinators for indexed families,
// that are used by programs such as SMT solvers. Lemmas provided in the rest of the library such as `Eq.lp` are implemented for
// fixed arities, and the implementation here aims to provide similar lemmas for N-ary Combinators.

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.HOL Stdlib.Nat Stdlib.Eq Stdlib.Impred;

inductive Sets : ℕ → TYPE ≔
| Unit : Sets 0
| ▹ : Π [n : ℕ], Set → Sets n → Sets (n +1);

notation ▹ infix right 10;

symbol sets (n : ℕ) : Set;
rule τ (sets $n) ↪ Sets $n;

// Type transformer x1 ▹ x2 ▹ .. into  x1 ⤳ x2 ⤳ ..
symbol arrows n : Sets n → Set → Set;
rule arrows 0 Unit $b ↪ $b
with arrows ($n +1) ($t ▹ $ts) $b ↪ $t ⤳ (arrows $n $ts $b);

injective symbol Arrow [n] (dom : Sets n) (cod : Set) : TYPE ≔ τ (@arrows n dom cod);

assert ⊢ Arrow (o ▹ o ▹ Unit) o ≡ (Prop → Prop → Prop);
assert ⊢ (∧) : Arrow (o ▹ o ▹ Unit) o;

// Tail of a telescope.
symbol tl [n] : Sets (n +1) → Sets n;
rule tl (_ ▹ $ts) ↪ $ts;


// The definitions below do not depend on these rules; they only let the `Sets`
// argument stay implicit at use sites such as `congₙ 2 (+)`.
// So the unif rule below  allows us to write generic programs acting on n-ary functions
// with less boilerplate.
// Unfolding `arrows` in the unifier. Its rules match on the `Sets` argument,
// so `arrows n ?ts ?b` is stuck when `?ts` is a metavariable: for
// `f : τ A → τ B → τ C` against `Arrow ?ts ?b`, the unifier faces
// `arrows 2 ?ts ?b ≡ A ⤳ B ⤳ C`. The rules below unfold it one step at a
// time, the constructor of `?ts`.
unif_rule @arrows ($n +1) $ts $b ≡ ($a ⤳ $c) ↪ [$ts ≡ @▹ $n $a _; @arrows $n (@tl $n $ts) $b ≡ $c];
unif_rule @arrows 0 $ts $b ≡ $c ↪ [$ts ≡ Unit; $b ≡ $c];

// Helper type constructor to just create an arrow of `n`-times the type `t`.
// Ex: SetsIdent 3 nat  ≡ nat ⤳ nat ⤳ nat
symbol SetsIdent n (t : Set) : Sets n;
rule SetsIdent 0 _ ↪ Unit
with SetsIdent ($n +1) $t ↪ $t ▹ (SetsIdent $n $t);

// Helper type constructor to just create an arrow of `n`-times the type `t`.
// Ex: ArrowI 2 nat  ≡ nat ⤳ nat ⤳ nat
symbol ArrowI n (a : Set) ≔ Arrow (SetsIdent n a) a; // Arrow wrapper for SetsIdent

// ------------------------------------------------------ pointwise liftings

// Lift a unary operation (τ A → τ B) to n-ary functions.
symbol lift [A B : Set] n [dom : Sets n] : (τ A → τ B) → Arrow dom A → Arrow dom B;
rule @lift _ _ 0 Unit $op $f ↪ $op $f
with @lift $A $B ($n +1) ($t ▹ $ts) $op $f ↪ λ (x : τ $t), @lift $A $B $n $ts $op ($f x);

// Lift a binary operation to two n-ary functions with the same domain
symbol lift2 [A B C : Set] n [dom : Sets n] :
  (τ A → τ B → τ C) → Arrow dom A → Arrow dom B → Arrow dom C;
rule @lift2 _ _ _ 0 Unit $op $f $g ↪ $op $f $g
with @lift2 $A $B $C ($n +1) ($t ▹ $ts) $op $f $g ↪
  λ (x : τ $t), @lift2 $A $B $C $n $ts $op ($f x) ($g x);

// `composeₙ n g f` precomposes the (n+1)-th argument of g with f:
// composition with f, lifted over the first n arguments.
symbol composeₙ [i j b : Set] n [dom : Sets n] (g : Arrow dom (j ⤳ b)) (f : τ i → τ j)
  : Arrow dom (i ⤳ b) ≔ lift n (λ h, h ∘ f) g;


symbol ∧ₙ [n] [dom : Sets n] (P Q : Arrow dom o) : Arrow dom o ≔ lift2 n (∧) P Q;

symbol ∨ₙ [n] [dom : Sets n] (P Q : Arrow dom o) : Arrow dom o ≔ lift2 n (∨) P Q;

symbol ⇒ₙ [n] [dom : Sets n] (P Q : Arrow dom o) : Arrow dom o ≔ lift2 n (⇒) P Q;

symbol quantₙ (Q : Π a : Set, (τ a → Prop) → Prop) n [ts : Sets n] : Arrow ts o → Prop;
rule @quantₙ _ 0 Unit $P ↪ $P
with @quantₙ $Q ($n +1) ($t ▹ $ts) $P ↪ $Q $t (λ (x : τ $t), @quantₙ $Q $n $ts ($P x));

symbol ∀ₙ n [ts : Sets n] (P : Arrow ts o) : Prop ≔ quantₙ (@∀) n P;
symbol ∃ₙ n [ts : Sets n] (P : Arrow ts o) : Prop ≔ quantₙ (@∃) n P;

// Cong n f g computes the statement
//   `∀ a₁, `∀ b₁, a₁ = b₁ ⇒ ... ⇒ `∀ aₙ, `∀ bₙ, aₙ = bₙ ⇒ f a₁ .. aₙ = g b₁ .. bₙ
symbol Cong n [ts : Sets n] [R : Set] (f g : Arrow ts R) : Prop;
rule @Cong 0 Unit $R $f $g ↪ @= $R $f $g
with @Cong ($n +1) ($t ▹ $ts) $R $f $g ↪
  `∀ (x : τ $t), `∀ (y : τ $t), (x = y) ⇒ @Cong $n $ts $R ($f x) ($g y);

opaque symbol congₙ [D : Set] n [ts : Sets n] (f : Arrow ts D) : π (@Cong n ts D f f) ≔
begin
  assume D n;
  refine ind_Sets (λ n u, `∀ f, @Cong n u D f f) _ _ n
  { reflexivity }
  { assume m t ts ih;
    assume f t1 t2 hrefl;
    rewrite hrefl;
    refine ih (f t2) }
end;

// Subst n P Q computes the statement
//   `∀ a₁, `∀ b₁, a₁ = b₁ ⇒ ... ⇒ `∀ aₙ, `∀ bₙ, aₙ = bₙ ⇒ P a₁ .. aₙ ⇒ Q b₁ .. bₙ
symbol Subst n [ts : Sets n] (P Q : Arrow ts o) : Prop;
rule @Subst 0 Unit $P $Q ↪ $P ⇒ $Q
with @Subst ($n +1) ($t ▹ $ts) $P $Q ↪
  `∀ (x : τ $t), `∀ (y : τ $t), (x = y) ⇒ @Subst $n $ts ($P x) ($Q y);

opaque symbol substₙ n [ts : Sets n] (P : Arrow ts o) : π (@Subst n ts P P) ≔
begin
  assume n;
  refine ind_Sets (λ n u, `∀ P, @Subst n u P P) _ _ n
  { assume P h; refine h }
  { assume m t ts ih;
    assume P x y hxy;
    rewrite hxy;
    refine ih (P y) }
end;

// Examples

private symbol f1 : Arrow (o ▹ o ▹ o ▹ o ▹ Unit) o;
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

private opaque symbol testSubst (P : Arrow (nat ▹ nat ▹ Unit) o) (a b x y : ℕ) :
  π (a = x) → π (b = y) → π (P a b) → π (P x y) ≔
begin assume P a b x y hax hby; refine substₙ 2 P _ _ hax _ _ hby end;