# ZX-Calculus in Lean 4

In-progress formalization of the ZX-calculus in Lean 4. 

[The ZX-calculus](https://zxcalculus.com/intro.html) is a graphical language for reasoning about quantum circuits and linear maps.

## What this project includes

- A dependently-typed abstract syntax tree (AST) for ZX diagrams
- An equational theory capturing the ZX-calculus rewrite rules
- Denotational semantics interpreting diagrams as linear maps between Hilbert spaces
- A thoerem library demonstrating simple verifiablity of ZX diagrams in Lean.

## Building

Requires [Lean 4 and Mathlib](https://lean-lang.org/install/). Build in this directory:

```bash
lake build
```

## Theorem Library

This repo also includes a theorem library `tests/` to check for correct implementation of the ZX-Calculus in Lean and to describe/prove various concepts in quantum computing. More TBD.

## References

- Bob Coecke and Aleks Kissinger. *Picturing Quantum Processes: A First Course in Quantum Theory and Diagrammatic Reasoning.* Cambridge University Press, 2017.

- PennyLane. "Introduction to the ZX-calculus." https://pennylane.ai/qml/demos/tutorial_zx_calculus

- Chris Heunen and Jamie Vicary. *Categories for Quantum Theory: An Introduction.* Oxford University Press, 2019. https://doi.org/10.1093/oso/9780198739623.001.0001
