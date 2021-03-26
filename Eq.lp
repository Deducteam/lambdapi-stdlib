// polymorphic Leibniz equality

require open Stdlib.Set Stdlib.Prop;

constant symbol = {a} : τ a → τ a → Prop;

notation = infix 1;

constant symbol eq_refl {a} (x:τ a) : π (x = x);
constant symbol eq_ind {a} {x y:τ a} : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ eq_ind;

// inequality

symbol ≠ {a} (x y : τ a) ≔ ¬ (x = y); // \neq

notation ≠ infix 1;

// symmetry

opaque symbol eq_sym {a} (x y:τ a) : π (x = y) → π (y = x) ≔
begin
  assume a x y xy;
  symmetry;
  apply xy;
end;
