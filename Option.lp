// option type

require open Stdlib.Set;

constant symbol option : Set → Set;

constant symbol none [a] : τ (option a);
constant symbol some [a] : τ a → τ (option a);
