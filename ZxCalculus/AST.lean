import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Abstract Syntax for ZX-Calculus

This file defines the abstract syntax (AST) for ZX-calculus diagrams, a graphical language
for reasoning about linear maps and quantum computations.

## Main Definitions

* `Generator n m`: The primitive generators of ZX-calculus with n input wires and m output wires
* `ZxTerm n m`: Composite ZX diagrams built from generators via sequential and parallel composition
* `dagger`: The adjoint (dagger/transpose) operation on ZX diagrams

## Notation

* `A ; B`: Sequential composition - connect outputs of A to inputs of B
* `A ⊗ B`: Parallel composition (tensor product) - place A and B side by side

## Implementation Notes

* Phases are represented as rational coefficients α where the actual phase is α*π
* The types are dependently typed - `ZxTerm n m` is a diagram with exactly n inputs and m outputs
* This ensures type-safe composition: can only compose `A ; B` when outputs of A match inputs of B
-/

open Real

/--
The primitive generators of the ZX-calculus, as an inductive type
indexed by number of input and output wires

### Structural Generators
* `empty`: The empty diagram (no wires)
* `id`: Identity wire
* `swap n m`: Permutes n wires with m wires

### Quantum Gates
* `H`: Hadamard gate (basis change between Z and X bases)
* `Z α n m`: Green (Z) spider with phase α*π, n inputs, m outputs
* `X α n m`: Red (X) spider with phase α*π, n inputs, m outputs

### Bell Pair Generators
* `cup`: Creates a Bell pair (2 maximally entangled qubits from nothing)
* `cap`: Bell state measurement (consumes 2 qubits, outputs nothing)
-/
inductive Generator : ℕ → ℕ → Type where
  /-- The empty diagram with no wires -/
  | empty : Generator 0 0
  /-- Identity wire (does nothing) -/
  | id : Generator 1 1
  /-- Swap/permutation: exchanges n wires with m wires -/
  | swap (n m : ℕ) : Generator (n + m) (m + n)
  /-- Hadamard gate: rotates between Z and X bases -/
  | H : Generator 1 1
  /-- Green spider (Z-basis) with phase α*π, n inputs, m outputs -/
  | Z (α : ℚ) (n m : ℕ) : Generator n m
  /-- Red spider (X-basis) with phase α*π, n inputs, m outputs -/
  | X (α : ℚ) (n m : ℕ) : Generator n m
  /-- Cup (creates Bell state): 0 → 2 -/
  | cup : Generator 0 2
  /-- Cap (Bell measurement): 2 → 0 -/
  | cap : Generator 2 0

/--
Composite ZX diagrams built from generators.
- A generator is a diagram
- If `A` and `B` are diagrams, `A ; B` is a diagram
- If `A` and `B` are diagrams, `A ⊗ B` is a diagram

### Constructors
* `gen g`: Lift a primitive generator to a diagram
* `comp A B`: Sequential composition `A ; B`
* `tens A B`: Parallel composition `A ⊗ B`
-/
inductive ZxTerm : ℕ → ℕ → Type where
  /-- Lift a generator to a diagram -/
  | gen {n m : ℕ} (g : Generator n m) : ZxTerm n m
  /-- Sequential composition: connect outputs of A to inputs of B -/
  | comp {n k m : ℕ} (A : ZxTerm n k) (B : ZxTerm k m) : ZxTerm n m
  /-- Parallel composition (tensor): place A and B side by side -/
  | tens {n₁ m₁ n₂ m₂ : ℕ} (A : ZxTerm n₁ m₁) (B : ZxTerm n₂ m₂) : ZxTerm (n₁ + n₂) (m₁ + m₂)

@[inherit_doc] infixl:90 " ; " => ZxTerm.comp

@[inherit_doc] infixl:80 " ⊗ " => ZxTerm.tens

namespace ZxTerm

/-! ### Smart Constructors

Construct basic ZX diagrams without explicitly using `gen` and `Generator` constructors.
-/

/-- The empty diagram (no wires) -/
def empty : ZxTerm 0 0 := ZxTerm.gen Generator.empty

/-- Identity wire -/
def id : ZxTerm 1 1 := ZxTerm.gen Generator.id

/-- Swap n wires with m wires -/
def swap (n m : ℕ) : ZxTerm (n + m) (m + n) := ZxTerm.gen (Generator.swap n m)

/-- Hadamard gate -/
def H : ZxTerm 1 1 := ZxTerm.gen Generator.H

/-- Z-spider with phase α*π, n inputs, m outputs -/
def Z (α : ℚ) (n m : ℕ) : ZxTerm n m := ZxTerm.gen (Generator.Z α n m)

/-- X-spider with phase α*π, n inputs, m outputs -/
def X (α : ℚ) (n m : ℕ) : ZxTerm n m := ZxTerm.gen (Generator.X α n m)

/-- Cup: creates a Bell state (0 → 2) -/
def cup : ZxTerm 0 2 := ZxTerm.gen Generator.cup

/-- Cap: Bell state measurement (2 → 0) -/
def cap : ZxTerm 2 0 := ZxTerm.gen Generator.cap

end ZxTerm

open ZxTerm

/--
The dagger of a ZX diagram.

Reverses the diagram by:
* Swapping inputs and outputs
* Negating phases on spiders
* Swapping cup ↔ cap
* Reversing sequential composition: (A ; B)† = B† ; A†
* Preserving parallel composition: (A ⊗ B)† = A† ⊗ B†

This operation corresponds to the adjoint of the linear map in the denotational semantics.
-/
def dagger {n m : ℕ} : ZxTerm n m → ZxTerm m n
  | .gen g => match g with
    | .empty => ZxTerm.gen Generator.empty
    | .id => ZxTerm.gen Generator.id
    | .swap n' m' => ZxTerm.gen (Generator.swap m' n')
    | .H => ZxTerm.gen Generator.H
    | .Z α n' m' => ZxTerm.gen (Generator.Z (-α) m' n')
    | .X α n' m' => ZxTerm.gen (Generator.X (-α) m' n')
    | .cup => ZxTerm.gen Generator.cap
    | .cap => ZxTerm.gen Generator.cup
  | f ; g => dagger g ; dagger f
  | f ⊗ g => dagger f ⊗ dagger g
