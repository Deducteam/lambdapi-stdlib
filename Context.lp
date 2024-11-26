/* Preliminary: alternative context-extension for dependent-types.
  This file will compare a usual traditional context-extension 
  (categories with families, etc) versus a more general and clearer 
  direct computational (strictified via Lambdapi rewrite rules) implementation 
  as required for a proof assistant for categories/sheaves/schemes
*/

/*  PRELIM: USUAL FORMULATION FOR TYPE THEORY

data Con : Set

postulate
  Ty : Con → ℕ → Set

infixl 2 _▹_
data Con where
  ◇ : Con
  _▹_ : (Γ : Con) → Ty Γ i → Con

postulate
  Sub : Con → Con → Set

postulate
  _∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  assoc : γ ∘ (δ ∘ θ) ≡ (γ ∘ δ) ∘ θ

  id : Sub Γ Γ
  idr : γ ∘ id ≡ γ
  idl : id ∘ γ ≡ γ

postulate
  _[_]ᵀ : Ty Γ i → Sub Δ Γ → Ty Δ i
  []ᵀ-∘ : A [ γ ∘ δ ]ᵀ ≡ A [ γ ]ᵀ [ δ ]ᵀ
  []ᵀ-id : A [ id ]ᵀ ≡ A

postulate
  Tm : (Γ : Con) → Ty Γ i → Set


postulate
  _[_]ᵗ : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ)
  []ᵗ-∘ : a [ γ ∘ δ ]ᵗ ≡[ ap-Tm []ᵀ-∘ ] a [ γ ]ᵗ [ δ ]ᵗ
  []ᵗ-id : a [ id ]ᵗ ≡[ ap-Tm []ᵀ-id ] a

postulate
  ε : Sub Δ ◇
  ε-∘ : ε ∘ γ ≡ ε
  ◇-η : id ≡ ε

  p : Sub (Γ ▹ A) Γ
  q : Tm (Γ ▹ A) (A [ p ]ᵀ)

  _,_ : (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ) → Sub Δ (Γ ▹ A)
  ,-∘ : (γ , a) ∘ δ ≡ (γ ∘ δ , coe (ap-Tm (sym []ᵀ-∘)) (a [ δ ]ᵗ))

  ▹-β₁ : p ∘ (γ , a) ≡ γ
  ▹-β₂ : q [ γ , a ]ᵗ ≡[ ap-Tm (sym []ᵀ-∘ ∙ ap-[]ᵀᵣ ▹-β₁) ] a
  ▹-η : id ≡ (p , q) ∈ Sub (Γ ▹ A) (Γ ▹ A)

  */

// MORE GENERAL AND CLEARED FORMULATION FOR CATEGORIES

constant symbol cat : TYPE ;

constant symbol func : Π (A B : cat), TYPE ;

constant symbol Id_func : Π [A : cat], func A A;
symbol ∘> : Π [A B C: cat], func A B → func B C → func A C;
notation ∘> infix left 90;

rule $X ∘> ($G ∘> $H) ↪ ($X ∘> $G) ∘> $H
with $F ∘> Id_func ↪ $F
with Id_func ∘> $F ↪ $F;

constant symbol Terminal_cat : cat;
injective symbol Terminal_func :  Π (A : cat), func A Terminal_cat;

rule (@∘> $A $B $C $F (Terminal_func $B)) ↪ (Terminal_func $A) ; 

rule (Terminal_func (Terminal_cat)) ↪ Id_func;

constant symbol catd: Π (X : cat), TYPE ; 

constant symbol Terminal_catd : Π (A : cat), catd A;

constant symbol funcd : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), TYPE ;

constant symbol  Id_funcd : Π [X : cat] [A : catd X], funcd A Id_func A;
symbol ∘>d: Π [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z], funcd A F B → funcd B G C → funcd A (F ∘> G) C;
notation ∘>d infix left 90;

rule $X ∘>d ($G ∘>d $H) ↪ ($X ∘>d $G) ∘>d $H
with $F ∘>d Id_funcd ↪ $F
with Id_funcd ∘>d $F ↪ $F; 

injective symbol Terminal_funcd :  Π [X Y: cat] (A : catd X) (xy : func X Y), funcd A xy (Terminal_catd Y);

rule ($FF ∘>d (Terminal_funcd $B $xy)) ↪ (Terminal_funcd _ _) ;
rule (Terminal_funcd (Terminal_catd _) Id_func) ↪ Id_funcd;

symbol Fibre_catd : Π [X I : cat] (A : catd X) (x : func I X), catd I;

rule Fibre_catd $A Id_func ↪ $A
with Fibre_catd $A ($x ∘> $y)  ↪ Fibre_catd (Fibre_catd $A $y) $x
with Fibre_catd (Terminal_catd _) _ ↪ (Terminal_catd _);

symbol Fibre_intro_funcd : Π [X I I' : cat] (A : catd X) (x : func I X) [J : catd I'] (i : func I' I) ,
 funcd J (i ∘> x) A  → funcd J i (Fibre_catd A x);

symbol Fibre_elim_funcd : Π [X I : cat] (A : catd X) (x : func I X), funcd (Fibre_catd A x) x A;

rule (Fibre_intro_funcd $A $x _ $FF) ∘>d (Fibre_elim_funcd $A $x) ↪ $FF ;
rule $HH ∘>d (Fibre_intro_funcd $A $x _ $FF) ↪ (Fibre_intro_funcd $A $x _ ($HH ∘>d $FF)) ;

rule Fibre_elim_funcd $A Id_func ↪ Id_funcd
with (Fibre_elim_funcd /* (Fibre_catd $A $y) */ _ $x) ∘>d Fibre_elim_funcd $A $y  ↪ Fibre_elim_funcd $A ($x ∘> $y);

rule Fibre_elim_funcd (Terminal_catd _) $xy ↪  (Terminal_funcd (Terminal_catd _) $xy) ;

rule Fibre_intro_funcd $A Id_func $i $FF ↪ $FF
// reverse direction?
with (Fibre_intro_funcd /* (Fibre_catd $A $y) */ _ $x $i (Fibre_intro_funcd $A $y /* ($i ∘> $x) */ _ $FF)) 
↪  (Fibre_intro_funcd $A ($x ∘> $y) $i $FF) 
// with (Fibre_intro_funcd $A ($x ∘> $y) $i $FF) 
// ↪ (Fibre_intro_funcd (Fibre_catd $A $y) $x $i (Fibre_intro_funcd $A $y ($i ∘> $x) $FF))
;

/* constant */ injective symbol Context_cat : Π [X : cat], catd X → cat;
/* constant */ injective symbol Context_proj_func : Π [X : cat] (A : catd X), func (Context_cat A) X;
injective symbol Context_proj2_funcd : Π [X : cat] (A : catd X), funcd (Terminal_catd _) (Context_proj_func A) A;
/* constant */ injective symbol Context_intro_func : Π [Y : cat] [B : catd Y] [X] (xy : func X Y),
funcd (Terminal_catd X) xy B → func X (Context_cat B);
/* constant */ injective symbol Context_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
funcd A xy B → func (Context_cat A) (Context_cat B); 

rule @Context_intro_func _ $A _ $xy $FF ∘> Context_proj_func $A ↪ $xy;

rule (@Context_func _ _ $A $B $F $FF) ∘> (Context_proj_func $B) 
↪ (Context_proj_func $A) ∘> $F;

rule @Context_intro_func _ $A _ $xy $GG ∘> (@Context_func _ _ $A $B $F $FF) 
↪ Context_intro_func _ ($GG ∘>d $FF);

rule (Terminal_funcd (Terminal_catd _) (@Context_intro_func _ $A _ $xy $GG)) ∘>d (Context_proj2_funcd $B) 
↪ $GG;

rule (@Context_func $X $Y $A $B $F $FF) ∘> (@Context_func $Y $Z $B $C $G $GG)
 ↪  Context_func ($FF ∘>d $GG);

rule Context_cat (Terminal_catd $A) ↪ $A;

rule Context_proj_func (Terminal_catd $A) ↪ Id_func;

rule Context_intro_func $xy (Terminal_funcd _ _) ↪ $xy;

rule Context_func (Id_funcd)  ↪ Id_func;

