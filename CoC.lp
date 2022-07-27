require open Blanqui.Lib.Set Blanqui.Lib.Prop;

// From CoC encoding, keep the following:
// For now this is only used in the proof of Pos.ind_positive_peano

constant symbol Type : TYPE;

symbol ε : Type → TYPE; // `e

symbol prop : Type;
rule ε prop ↪ Prop;

symbol set : Type;
rule ε set ↪ Set;

constant symbol ∀ₛₛ (a : Set)  : (τ a → Set)  → Set; // \forall__s__s
constant symbol ∀ₚₛ (P : Prop) : (π P → Set)  → Set;

// constant symbol ∀ₛₚ (a : Set)  : (τ a → Prop) → Prop; // this is ∀
constant symbol ∀ₚₚ (P : Prop) : (π P → Prop) → Prop; // ⇒ is the non-dependent version

constant symbol ∀ₛₜ (a : Set)  : (τ a → Type) → Type;
constant symbol ∀ₚₜ (P : Prop) : (π P → Type) → Type;
constant symbol ∀ₜₚ (T : Type) : (ε T → Prop) → Prop;
constant symbol ∀ₜₛ (T : Type) : (ε T → Set)  → Set;
constant symbol ∀ₜₜ (T : Type) : (ε T → Type) → Type;

rule τ (∀ₛₛ $s $f) ↪ Π a : τ $s, τ ($f a);
rule τ (∀ₚₛ $p $f) ↪ Π P : π $p, τ ($f P);

// rule π (∀ₛₚ $s $f) ↪ Π a : τ $s , π ($f a); // already defined
rule π (∀ₚₚ $p $f) ↪ Π P : π $p, π ($f P); // defined for ⇒

rule ε (∀ₛₜ $s $f) ↪ Π a : τ $s, ε ($f a);
rule ε (∀ₚₜ $p $f) ↪ Π P : π $p, ε ($f P);
rule π (∀ₜₚ $t $f) ↪ Π T : ε $t, π ($f T);
rule τ (∀ₜₛ $t $f) ↪ Π a : ε $t, τ ($f a);
rule ε (∀ₜₜ $t $f) ↪ Π T : ε $t, ε ($f T);
