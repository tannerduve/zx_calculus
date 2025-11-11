# ZX-Calculus in Lean 4

In-progress formalization of the ZX-calculus in Lean 4. 

[The ZX-calculus](https://zxcalculus.com/intro.html) is a graphical language for reasoning about quantum circuits and linear maps.

## Overview
This project provides:

- A dependently-typed abstract syntax tree (AST) for ZX diagrams
- An equational theory capturing the ZX-calculus rewrite rules
- Denotational semantics interpreting diagrams as linear maps between Hilbert spaces

## Project Structure

```
ZxCalculus/
├── AST.lean                    # ZX diagram syntax (generators and terms)
├── RewriteTerm.lean            # Equational theory and rewrite rules
├── DenotationalSemantics.lean  # Interpretation as linear maps
```

## Main Components

### AST (`ZxCalculus/AST.lean`)

Defines the syntax of ZX diagrams:
- **Generators**: Basic building blocks (empty, identity, swap, Hadamard, Z/X spiders, cup/cap)
- **ZxTerm**: Inductively defined diagrams with sequential (`;`) and parallel (`⊗`) composition
- **Dependent types**: Each diagram has a type `ZxTerm n m` representing n inputs and m outputs

### Rewrite Rules (`ZxCalculus/RewriteTerm.lean`)

Defines `ZxEquiv`, an inductive equivalence relation encoding:
- Symmetric monoidal category structure (associativity, units, interchange)
- ZX-calculus specific rules:
  - Spider fusion (composing spiders adds phases)
  - Color change (Hadamard conjugation swaps Z/X spiders)
  - π-copy rules (phase π spiders commute with opposite-color spiders)

### Denotational Semantics (`ZxCalculus/DenotationalSemantics.lean`)

Interprets ZX diagrams as linear maps (matrices):
- Maps n-wire diagrams to matrices representing linear operators on ℂ^(2^n)
- Uses Mathlib's matrix operations including Kronecker product for tensor composition
- Defines `interp : ZxTerm n m → LinMap n m` where `LinMap n m := Matrix (Fin (2^m)) (Fin (2^n)) ℂ`
- Implemented generators: identity, empty, swap, Hadamard gate

## Status
Current implementation includes:

**Completed:**
- Core AST with dependent types
- Structural axioms (monoidal category laws)
- Basic ZX rewrite rules (spider fusion, color change, π-copy)
- Matrix-based denotational semantics framework
- Basic generators: identity, empty, swap (permutation), Hadamard gate
- Sequential composition (matrix multiplication) and parallel composition (Kronecker product)

**In Progress:**
- Z and X spider interpretations (parameterized by phase angle)
- Cup and cap generators (Bell states and effects)
- Additional rewrite rules (bialgebra, Euler decomposition, Hopf)
- Better diagram-like notation

**To prove:**
- Soundness: if a diagram `A` rewrites to a diagram `B`, then they represent the same linear map. ie. (`A` --> `B`) ==> `[[A]] == [[B]]`
- Completeness: Every linear map representable in ZX-calculus has a corresponding diagram

## Building

Requires [Lean 4 and Mathlib](https://lean-lang.org/install/). Build with in this directory:

```bash
lake build
```

## Theorem Library

This repo also includes a theorem library `tests/` to check for correct implementation of the ZX-Calculus in Lean and to describe/prove various concepts in quantum computing. More TBD.
