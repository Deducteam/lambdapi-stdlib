Standard library of [Lambdapi](https://github.com/Deducteam/lambdapi)
=====================================================================

- `Bool`: booleans
- `Classic`: classical logic
- `Comp`: comparison datatype
- `Conj`: varyadic conjunction
- `Coprod`: disjoint sum
- `DepProd`: dependent pairs
- `Disj`: varyadic disjunction
- `Epsilon`: Hilbert choice operator
- `Eq`: polymorphic Leibniz equality
- `ExtraRules`: additional rewrite rules derived from proved equalities
- `FOL`: polymorphic first-order logic
- `FunExt`: require open Stdlib.Eq Stdlib.HOL;
- `HOL`: higher-order logic
- `Impred`: impredicativity (quantification on propositions)
- `List`: polymorphic lists
- `NaryFun`: n-ary functions and relations
- `Nat`: unary natural numbers
- `Option`: option type
- `Pos`: positive binary integers
- `Prod`: Cartesian product
- `PropExt`: propositional extensionality
- `Prop`: propositional logic
- `QuotientExample`: example of quotient type
- `Quotient`: quotient types
- `Set`: type of type codes
- `String`: builtin string type
- `Subset`: subset types
- `Tactic`: tactic type
- `Univ`: universes
- `Z`: binary integers

The libraries on natural numbers and polymorphic lists follow the
corresponding Rocq SSReflect libraries [ssrnat.v](https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/ssrnat.v)
and [seq.v](https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/seq.v). The library on integers follow the one of the Rocq standard library.

Installation with Opam
----------------------

```
opam repository -a --set-default add lambdapi https://github.com/deducteam/opam-lambdapi-repository.git # once
opam install lambdapi-stdlib
```

Usage in Lambdapi
-----------------

```
require open Stdlib.Nat;
```

Compilation from the sources
----------------------------

```
opam install --deps-only . # once
make
```

Installation from the sources
-----------------------------

```
opam install .
```
