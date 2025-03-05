require open Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.FOL Stdlib.HOL;

symbol funExt [a b] (f g : τ (a ⤳ b)) : π(`∀ x, f x = g x) → π(f = g);

