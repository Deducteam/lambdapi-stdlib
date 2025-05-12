// builtin type of strings

require open Stdlib.Set;

constant symbol String : TYPE;
builtin "String" ≔ String;

constant symbol string : Set;
rule τ string ↪ String;
