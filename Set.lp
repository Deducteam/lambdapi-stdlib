// Type of set codes for quantifying over sets (polymorphism)

constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // \tau

builtin "T" ≔ τ;
