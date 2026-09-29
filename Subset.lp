// Subset types: a dependent pair of an element and a proof

require open Stdlib.Prop Stdlib.Set Stdlib.Eq Stdlib.FOL;

[a: Set] (p: τ a → Prop) inductive Subset : TYPE ≔
  mk (x: τ a) : π (p x) → Subset p;

symbol elt [a] [p] (e: @Subset a p) : τ a;

rule elt (mk $x _) ↪ $x;

symbol prf [a] [p] (e: @Subset a p) : π (p (elt e));

rule prf (mk _ $h) ↪ $h;

opaque symbol Subset_∃ [a] [p] (e: @Subset a p) : π (`∃ x, p x) ≔
begin assume a p e; refine ∃ᵢ (elt e) (prf e) end;

/* The `subset` Set-constructor requires an existential proof: this is needed
   to be consistent with the axiom `el` of Set.lp stating that every set is
   non-empty. */

constant symbol subset [a] (p: τ a → Prop) : π (`∃ x, p x) → Set;

rule τ (@subset $a $p _) ↪ @Subset $a $p;

opaque symbol Subset_η [a] [p] [h] (e: τ (@subset a p h)) :
  π (mk (elt e) (prf e) = e) ≔
begin assume a p h; induction; assume x hx; reflexivity end;

opaque symbol eq_elt [a] [p] [h] (x y: τ (@subset a p h)) :
  π (x = y) → π (elt x = elt y) ≔
begin assume a p h x y e; refine feq (λ z, elt z) e end;

opaque symbol mk_inj [a] [p] [h] (x y: τ a) (hx: π (p x)) (hy: π (p y)) :
  π (@= (@subset a p h) (mk x hx) (mk y hy)) → π (x = y) ≔
begin assume a p h x y hx hy e; refine @eq_elt a p h (mk x hx) (mk y hy) e end;
