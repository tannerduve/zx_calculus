# ZX-Calculus in Lean 4

In-progress formalization of the ZX-calculus in Lean 4, a graphical language for reasoning about quantum circuits and linear maps.

## Overview

The ZX-calculus is a graphical language that represents quantum computations and linear maps as diagrams. This project provides:

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

Interprets ZX diagrams as linear maps:
- Maps n-wire diagrams to linear operators on ℂ^(2^n)
- Uses Mathlib's `PiLp` for Hilbert space structure
- Defines `interp : ZxTerm n m → LinMap n m`

## Status
Current implementation includes:

**Completed:**
- Core AST with dependent types
- Structural axioms (monoidal category laws)
- Basic ZX rewrite rules (spider fusion, color change, π-copy)
- Denotational semantics framework

**In Progress:**
- Complete generator interpretations (H, Z/X spiders, cup/cap)
- Tensor product of linear maps
- Additional rules (bialgebra, Euler decomposition, Hopf)
- Soundness proof (rewrite rules preserve semantics)
- Better diagram-like notation

**Planned:**
- Completeness results


## Building

Requires Lean 4 and Mathlib. Build with:

```bash
lake build
```
