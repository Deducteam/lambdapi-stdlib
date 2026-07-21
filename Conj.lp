/* Library on Meta-Theorems for Conjunctions

-------------------

The library proves the following meta-theorems:

** n-ary Natural Deduction rules:
   - ∧ᵢₙ is the n-ary version of the introduction rule for ∧.
   - ∧ₑₙ is the n-ary version of the elimination rule for ∧.

---

** Defined Operations:
           `x ∈ₙ l`: Special case of ∈ for natural numbers and equality relation `eqn`
       `clause n l`: Returns the element of the list `l` of terms of type `o` at index `n`.
           `conj l`: Returns the conjunction of all terms of type `o` in the list `l`.
*/

require open Stdlib.List Stdlib.PropExt;

////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////// lemmas ////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Define some notations corresponding to standard library symbols
symbol ∈ₙ ≔ ∈ eqn;
notation ∈ₙ infix right 40;

symbol clause ≔ nth ⊥;

opaque symbol clause_ext (l: 𝕃 o) (l0 : τ o) (n: τ nat) : 
    π (clause l n) → π (clause (l0 ⸬ l) (n +1)) ≔
begin
    assume l l0 n h1;
    refine h1
end;


// n-ary conjunction

symbol conj : 𝕃 o → τ o;
rule conj ($l1 ⸬ ($c ⸬ $l)) ↪ $l1 ∧ conj ($c ⸬ $l)
with conj ($l1 ⸬ □) ↪ $l1 
with conj □ ↪ ⊤;

assert l0 l1 l2 ⊢ π (conj (l0 ⸬ l1 ⸬ l2  ⸬ l1 ⸬ □)) ≡ π (l0 ∧ (l1 ∧ (l2  ∧ l1)));

opaque symbol conj_head (c0 : τ o) (c : 𝕃 o) : 
     π (conj (c0 ⸬ c)) → π c0 ≔
begin
    assume c0;
    induction
        {assume h1;
        refine h1}   
        {assume x0 c1 h1 h2;
        refine ∧ₑ₁ h2}
end; 

opaque symbol conj_tail (c0 : τ o) (c : 𝕃 o) : 
     π (conj (c0 ⸬ c)) → π (conj c) ≔
begin
    assume c0;
    induction
        {assume h1;
        refine ⊤ᵢ}   
        {assume x0 c1 h1 h2; 
        refine ∧ₑ₂ h2}
end; 

opaque symbol conj_correct (c0 : τ o) (c : 𝕃 o) : 
    π (conj (c0 ⸬ c)) → π (c0 ∧ conj c) ≔
begin
    assume c0;
    induction
        {assume h1;
        refine ∧ᵢ h1 ⊤ᵢ}
        {assume x1 c1 h1 h2;
        refine h2}
end;

opaque symbol conj_sound (c0 : τ o) (c : 𝕃 o) : 
    π (c0 ∧ conj c) →  π (conj (c0 ⸬ c)) ≔
begin
    assume c0;
    induction
        {assume h1; refine ∧ₑ₁ h1}
        {assume x1 c1 h1 h2; refine h2}
end;


////////////////////////////////////////////////////////////////////////////////
///////////////////////////////// meta-theorems ////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// ∧ᵢₙ 
opaque symbol ∧ᵢₙ (c0 : 𝕃 o) (c1 : 𝕃 o) : 
    π (conj c0) → π (conj c1) → π (conj (c0 ++ c1))≔
begin
    induction
        {assume x h0 h1;
        refine h1}
        {assume x0 l0 h0 l1 h1 h2;
        refine conj_sound x0 (l0 ++ l1) _;
        refine ∧ᵢ _ _
            {refine conj_head x0 l0 h1}
            {refine h0 l1 (conj_tail x0 l0 h1) h2}}
end;

// ∧ₑₙ 
opaque symbol ∧ₑₙ (id : τ nat) (cnf: 𝕃 o) : 
    π (id ∈ₙ indexes cnf) → π (conj cnf) → π (clause cnf id) ≔
begin
    induction 
        {induction
            {assume h0 h1; refine h0}
            {assume x cnf h0 h1 h2; 
            refine conj_head x cnf h2}}
        {assume id h0;
        induction
            {assume b; refine ⊥ₑ b}
            {assume x cnf h1 h2 h3;
            have ConjImpCl : π (conj cnf ⇒ clause cnf id)
                {refine h0 cnf (indexes_decrement id x cnf h2)};
            refine clause_ext cnf x id (ConjImpCl (conj_tail x cnf h3))}}
end;