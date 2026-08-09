/* Preliminary: alternative context-extension for dependent-types.
  This file will compare a usual traditional context-extension 
  (categories with families, etc) versus a more general and clearer 
  direct computational (strictified via Lambdapi rewrite rules) implementation 
  as required for a proof assistant for categories/sheaves/schemes
*/

/*****************************************
* # PRELIMINARIES REMINDERS ABOUT DEPENDENT TYPES
* AND IMPLEMENTING CONTEXT-EXTENSION 
* (CATEGORIES WITH FAMILIES) WHICH COMPUTES
******************************************/

constant symbol 
  Con : TYPE;

constant symbol
  Ty : Con → TYPE;

constant symbol
  ◇ : Con;

injective symbol
  ▹ : Π (Γ : Con), Ty Γ → Con;

notation ▹ infix right 90;

constant symbol
  Sub : Con → Con → TYPE;

symbol
  ∘ : Π [Δ Γ Θ], Sub Δ Γ → Sub Θ Δ → Sub Θ Γ;

notation ∘ infix right 80;

rule /* assoc */ 
  $γ ∘ ($δ ∘ $θ) ↪ ($γ ∘ $δ) ∘ $θ;

constant symbol
  id : Π [Γ], Sub Γ Γ;

rule /* idr */ 
  $γ ∘ id ↪ $γ
with /* idl */ 
  id ∘ $γ ↪ $γ;

symbol
  'ᵀ_ : Π [Γ Δ], Ty Γ → Sub Δ Γ → Ty Δ;

notation 'ᵀ_ infix left 70;

rule /* 'ᵀ_-∘ */ 
  $A 'ᵀ_ $γ 'ᵀ_ $δ ↪ $A 'ᵀ_( $γ ∘ $δ )
with /* 'ᵀ_-id */
  $A 'ᵀ_ id ↪ $A;

constant symbol
  Tm : Π (Γ : Con), Ty Γ → TYPE;

symbol
  'ᵗ_ : Π [Γ A Δ], Tm Γ A → Π (γ : Sub Δ Γ), Tm Δ (A 'ᵀ_ γ);

notation 'ᵗ_ infix left 70;

rule /*  'ᵗ_-∘ */ 
  $a 'ᵗ_ $γ 'ᵗ_ $δ ↪ $a 'ᵗ_( $γ ∘ $δ )
with /* 'ᵗ_-id */ 
  $a 'ᵗ_ id ↪ $a;

injective symbol
  ε : Π [Δ], Sub Δ ◇;

rule /* ε-∘ */
  ε ∘ $γ ↪ ε
with /* ◇-η */
  @ε ◇ ↪ id;

injective symbol 
  pₓ : Π [Γ A], Sub (Γ ▹ A) Γ;

injective symbol 
  qₓ : Π [Γ A], Tm (Γ ▹ A) (A 'ᵀ_ pₓ);

injective symbol 
  &ₓ : Π [Γ Δ A], Π (γ : Sub Δ Γ), Tm Δ (A 'ᵀ_ γ) → Sub Δ (Γ ▹ A);

notation &ₓ infix left 70;

rule /*  &ₓ-∘ */
  ($γ &ₓ $a) ∘ $δ ↪ ($γ ∘ $δ &ₓ ($a 'ᵗ_ $δ));

rule /*  ▹-β₁ */ 
  pₓ ∘ ($γ &ₓ $a) ↪ $γ;

rule /* ▹-β₂ */ 
  qₓ 'ᵗ_ ($γ &ₓ $a) ↪ $a;

rule /* ▹-η */
  (@&ₓ _ _ $A (@pₓ _ $A) qₓ) ↪ id;


/*****************************************
* # CATEGORIES, FUNCTORS, ISOFIBRATIONS OF CATEGORIES
******************************************/

constant symbol cat : TYPE;

constant symbol func : Π (A B : cat), TYPE;

constant symbol catd: Π (X : cat), TYPE;

constant symbol funcd : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), TYPE;

/* -----
* ## categories and functors (objects) */

constant symbol Terminal_cat : cat;

constant symbol Id_func : Π [A : cat], func A A;

symbol ∘> : Π [A B C: cat], func A B → func B C → func A C;
notation ∘> infix left 90; // compo_func

rule $X ∘> ($G ∘> $H) ↪ ($X ∘> $G) ∘> $H
with $F ∘> Id_func ↪ $F
with Id_func ∘> $F ↪ $F;

injective symbol Terminal_func :  Π (A : cat), func A Terminal_cat;

rule (@∘> $A $B $C $F (Terminal_func $B)) ↪ (Terminal_func $A)
with (Terminal_func (Terminal_cat)) ↪ Id_func;

/* -----
* ## fibred (dependent) categories */

constant symbol Terminal_catd : Π (A : cat), catd A;

symbol Fibre_catd : Π [X I : cat] (A : catd X) (x : func I X), catd I;

rule Fibre_catd $A Id_func ↪ $A
with Fibre_catd $A ($x ∘> $y) ↪ Fibre_catd (Fibre_catd $A $y) $x;
rule Fibre_catd (Terminal_catd _) _ ↪ (Terminal_catd _);

/* -----
* ## fibred (dependent) functors */

constant symbol Id_funcd : Π [X : cat] [A : catd X], funcd A Id_func A;

symbol ∘>d: Π [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z], funcd A F B → funcd B G C → funcd A (F ∘> G) C;
notation ∘>d infix left 90; // compo_funcd

rule $X ∘>d ($G ∘>d $H) ↪ ($X ∘>d $G) ∘>d $H
with $F ∘>d Id_funcd ↪ $F
with Id_funcd ∘>d $F ↪ $F;

injective symbol Terminal_funcd :  Π [X Y: cat] (A : catd X) (xy : func X Y), funcd A xy (Terminal_catd Y);

injective symbol Fibre_intro_funcd : Π [X I I' : cat] (A : catd X) (x : func I X) [J : catd I'] (i : func I' I) ,
 funcd J (i ∘> x) A → funcd J i (Fibre_catd A x);

injective symbol Fibre_elim_funcd : Π [X I : cat] (A : catd X) (x : func I X), funcd (Fibre_catd A x) x A;

// naturality
rule $HH ∘>d (Fibre_intro_funcd $A $x _ $FF) ↪ (Fibre_intro_funcd $A $x _ ($HH ∘>d $FF))
with (Fibre_elim_funcd /*DON'T SPECIFY, ALLOW CONVERSION: (Fibre_catd $A $y) */ _ $x) ∘>d Fibre_elim_funcd $A $y
 ↪ Fibre_elim_funcd $A ($x ∘> $y);

// beta, eta
rule (Fibre_intro_funcd $A $x _ $FF) ∘>d (Fibre_elim_funcd $A $x) ↪ $FF
with (Fibre_intro_funcd $A $x Id_func (Fibre_elim_funcd $A $x)) ↪ Id_funcd;

rule Fibre_elim_funcd $A Id_func ↪ Id_funcd
with Fibre_intro_funcd $A Id_func $i $FF ↪ $FF
with (Fibre_intro_funcd /* (Fibre_catd $A $y) */ _ $x $i (Fibre_intro_funcd $A $y /* ($i ∘> $x) */ _ $FF)) 
↪ (Fibre_intro_funcd $A ($x ∘> $y) $i $FF);

rule (Terminal_funcd (Terminal_catd _) $xy) ↪ Fibre_elim_funcd (Terminal_catd _) $xy;
rule ($FF ∘>d (Terminal_funcd $B $xy)) ↪ (Terminal_funcd _ _);
rule (Terminal_funcd (Terminal_catd _) Id_func) ↪ Id_funcd; // confluent...


/*****************************************
* # CONTEXT EXTENSION FOR CATEGORIES
******************************************/

injective symbol Context_cat : Π [X : cat], catd X → cat;

injective symbol Context_elimCat_func : Π [X : cat] (A : catd X), func (Context_cat A) X;

injective symbol Context_elimCatd_funcd : Π [X : cat] (A : catd X), funcd (Terminal_catd _) (Context_elimCat_func A) A;

injective symbol Context_intro_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
funcd A xy B → func (Context_cat A) (Context_cat B);

rule Context_cat (Terminal_catd $A) ↪ $A;
rule Context_elimCat_func (Terminal_catd $A) ↪ Id_func;
rule Context_elimCatd_funcd (Terminal_catd $A) ↪ Id_funcd;
rule Context_intro_func (Id_funcd) ↪ Id_func
with Context_intro_func (Terminal_funcd $A $xy) ↪ Context_elimCat_func $A ∘> $xy;

// definable symbols
injective symbol Context_intro_single_func [Y : cat] [B : catd Y] [X] (xy : func X Y)
(FF : funcd (Terminal_catd X) xy B) : func X (Context_cat B);
rule Context_intro_single_func _ $FF ↪ @Context_intro_func _ _ (Terminal_catd _) _ _ $FF;

injective symbol Context_intro_congr_func [Y : cat] [B : catd Y] [X] (xy : func X Y) 
: func (Context_cat (Fibre_catd B xy)) (Context_cat B);
rule Context_intro_congr_func $xy ↪ Context_intro_func (Fibre_elim_funcd _ $xy);

// beta rules
rule (@Context_intro_func _ _ $A $B $F $FF) ∘> (Context_elimCat_func $B) 
↪ (Context_elimCat_func $A) ∘> $F;
rule (Fibre_elim_funcd (Terminal_catd $X) (@Context_intro_func _ _ (Terminal_catd $X) $B $xy $FF)) ∘>d (Context_elimCatd_funcd $B) 
↪ $FF;

// LAMBDAPI BUG? this unification rule doesnt work... so finding an alternative
// unif_rule Context_cat $B ≡ (Context_cat (Terminal_catd (Context_cat $X))) ↪ [ $B ≡ $X];
symbol rule_Context_cat_Terminal_catd_func [X: cat] (A: catd X) 
: func (Context_cat (Terminal_catd (Context_cat A))) (Context_cat A)
≔ begin assume X A; simplify; refine Id_func; end;

// eta rules
rule Context_intro_func (Context_elimCatd_funcd $A) 
 ↪ rule_Context_cat_Terminal_catd_func $A;
rule @Context_intro_func _ _ _ _ $xy (Fibre_elim_funcd (Terminal_catd _) _) ↪ $xy;

// naturality rules
// confluent ... and both rules required despite in meta the latter conversion is derivable from the former rules
rule (@Context_intro_func $X $Y $A $B $F $FF) ∘> (@Context_intro_func $Y $Z $B $C $G $GG)
 ↪ Context_intro_func ($FF ∘>d $GG)
with $z ∘> @Context_intro_func _ _ (Terminal_catd _) _ _ $FF
↪ Context_intro_func ( (Fibre_elim_funcd (Terminal_catd _) $z)  ∘>d $FF );

assert [X Y : cat] [B : catd Y] [xy : func X Y] (FF : funcd (Terminal_catd X) xy B) [Z] [z : func Z X] ⊢  
(@Context_intro_func _ _ _ _ z (Terminal_funcd (Terminal_catd Z) z)) ∘> Context_intro_func FF
 ≡ Context_intro_func ( (Terminal_funcd (Terminal_catd Z) z)  ∘>d FF );

/* voila */
