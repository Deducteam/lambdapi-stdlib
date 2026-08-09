// Prop
builtin "fold_imp" ≔ {|fold_⇒|};
builtin "eqv_refl" ≔ {|⇔_refl|};
builtin "eqv_sym" ≔ {|⇔_sym|};
builtin "eqv_trans" ≔ {|⇔_trans|};

// Classic
builtin "not_not_elim" ≔ {|¬¬ₑ|};
builtin "or_not_intro" ≔ {|∨¬ᵢ|};
builtin "ex_not_intro" ≔ {|∃¬ᵢ|};

// Bool
builtin "ind_bool" ≔ {|ind_𝔹|};
builtin "case_bool" ≔ {|case_𝔹|};
builtin "ind_bool_eq" ≔ {|ind_𝔹_eq|};
builtin "istrue_eq_true" ≔ {|istrue=true|};
builtin "true_eq_istrue" ≔ {|true=istrue|};
builtin "not_istrue_eq_false" ≔ {|¬istrue=false|};
builtin "false_eq_not_istrue" ≔ {|false=¬istrue|};
builtin "false_neq_true" ≔ {|false≠true|};
builtin "true_neq_false" ≔ {|true≠false|};
builtin "not_istrue" ≔ {|¬_istrue|};
builtin "or_istrue" ≔ {|∨_istrue|};
builtin "or_intro1" ≔ {|orᵢ₁|};
builtin "or_intro2" ≔ {|orᵢ₂|};
builtin "or_elim" ≔ {|orₑ|};
builtin "and_istrue" ≔ {|∧_istrue|};
builtin "and_intro" ≔ {|andᵢ|};
builtin "and_elim1" ≔ {|andₑ₁|};
builtin "and_elim2" ≔ {|andₑ₂|};

// Nat
builtin "geb" ≔ {|≥|};
builtin "gtb" ≔ >;
builtin "exp" ≔ ^;
builtin "factorial" ≔ !;

// List
builtin "In_nat" ≔ {|∈ₙ|};
builtin "is_nil" ≔ {|is□|};
builtin "incl" ≔ {|⊆|};
builtin "incl_nat" ≔ {|⊆ₙ|};
