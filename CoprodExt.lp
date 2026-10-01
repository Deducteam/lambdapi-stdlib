/* Properties of the co-Cartesian product that require the extensionality of the Cartesian product. */

require open Stdlib.ProdExt Stdlib.Coprod;

opaque symbol undist_dist_× [a b c] (x: τ (a × sum b c)) :
  π (undist_× (dist_× x) = x) ≔
begin
  assume a b c x; rewrite prodExt x; refine undist_dist_‚ (x ₁) (x ₂)
end;

opaque symbol dist_undist_× [a b c] (s: τ (sum (a × b) (a × c))) :
  π (dist_× (undist_× s) = s) ≔
begin
  assume a b c; induction
  { assume u; symmetry; refine feq inl (prodExt u) }
  { assume v; symmetry; refine feq inr (prodExt v) }
end;
