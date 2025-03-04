require open Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.FOL Stdlib.HOL;

symbol funExt [T S] (f g : τ (T ⤳ S)) : π(`∀ x, f x = g x) → π(f = g);

