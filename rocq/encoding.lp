// symbols used for encoding simple type theory

builtin "Set" ≔ Set.Set;
builtin "El" ≔ Set.{|τ|};
builtin "arr" ≔ Set.{|⤳|};
builtin "prop" ≔ Prop.Prop;
builtin "Prf" ≔ Prop.{|π|};
builtin "imp" ≔ Prop.{|⇒|};
builtin "not" ≔ Prop.{|¬|};
builtin "or" ≔ Prop.{|∨|};
builtin "and" ≔ Prop.{|∧|};
builtin "eq" ≔ Eq.=;
builtin "all" ≔ FOL.{|∀|};
builtin "ex" ≔ FOL.{|∃|};
