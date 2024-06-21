Standard library of [Lambdapi](https://github.com/Deducteam/lambdapi)
=====================================================================

- `Prop`: propositional logic
- `Eq`: equality
- `Set`: set codes for polymorphism
- `FOL`: typed first-order logic
- `Bool`: booleans
- `Nat`: natural numbers
- `List`: polymorphic lists
- `Classic`: classical logic

The libraries on natural numbers and polymorphic lists follow the
corresponding Coq SSReflect libraries:

- [ssrnat.v](https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/ssrnat.v)

- [seq.v](https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/seq.v)

Installation with Opam
----------------------

```
opam repository -a add lambdapi https://github.com/deducteam/opam-lambdapi-repos
itory.git # once
opam install lambdapi-stdlib
```

Usage in Lambdapi
-----------------

```
require open Stdlib.Prop Stdlib.Set Stdlib.FOL Stdlib.Nat /* ... */;
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
