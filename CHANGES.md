All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## 1.3.1

### Fixed

- declare theorems as opaque symbols

## 1.3.0

### Added

- FunExt: axiom for functional extensionality
- PropExt: axiom for propositional extensionality and related theorems
- Prod: Cartesian product (extracted from Set)
- Option: polymorphic option type
- String: builtin string type
- Tactic: tactic type for the eval tactic
- Comp: isLe and isGe
- List: mem_tail, nths and related properties
- Bool: istrue=true

### Changed

- Set: moved Cartesian product to separate Prod file, pairing constructor renamed as "‚"

## 1.2.0 (2025-02-04)

### Added

- HOL: Set constructor ⤳ for quantifying over function types
- Impred: Set constructor o for quantifying over propositions
- Epsilon: Hilbert's ε operator
- List: add iota and indexes
- Set: add ι:Set and an axiom el:Π a,τ a saying that every set is non-empty 
- Pos, Z: add printing to decimal notation

### Changed

- Z: rename × into *, and ~ into —
- Z: add parsing from decimal notation
- Nat: rename 0 into _0, and -1 into ∸1
- Bool: declare istrue as injective

### Fixed

- Z: missing notation for ≥

## 1.1.0 (2024-06-21)

- Classic: classical logic
- Prop: rename top into ⊤ᵢ
- FOL: declare more arguments of ∃ᵢ and ∃ₑ implicit

## 1.0.0 (2023-10-19)

- Z: integers (Quentin Garchery)

## 0.0.0 (2022-01-27)

- Nat, List: natural numbers and lists (Quentin Buzet)
