import ZxCalculus.AST
import ZxCalculus.RewriteTerm

/-!
# Quantum Gates

Standard gates for quantum computing in ZX-calculus.

## Clifford+T Gates (Fault-Tolerant Universal Set)
* `T`: π/4 Z-rotation (non-Clifford, makes gate set universal)
* `S`: π/2 Z-rotation (Clifford gate)
* `CNOT`: Controlled-NOT (Clifford gate)

## Parameterized Rotations
* `Rz θ`: Z-rotation by angle θ·π
* `Rx θ`: X-rotation by angle θ·π
* `CRz θ`: Controlled Z-rotation by angle θ·π

Clifford+T is the standard for fault-tolerant quantum computing.
Parameterized rotations are essential for variational quantum algorithms (VQE, QAOA).
-/

open ZxTerm

/-! ## Parameterized Rotations -/

/-- Rz(θ): Z-rotation by angle θ·π -/
def Rz (θ : ℚ) : ZxTerm 1 1 := Z θ 1 1

/-- Rx(θ): X-rotation by angle θ·π -/
def Rx (θ : ℚ) : ZxTerm 1 1 := X θ 1 1

/-- CRz(θ): Controlled Z-rotation by angle θ·π.
    Generalizes controlled-S and controlled-T gates. -/
def CRz (θ : ℚ) : ZxTerm 2 2 := Z θ 2 2

/-! ## Clifford+T Gates -/

/-- T gate: π/4 Z-rotation. Non-Clifford gate required for universality. -/
def T : ZxTerm 1 1 := Rz (1/4)

/-- S gate: π/2 Z-rotation. Clifford gate. -/
def S : ZxTerm 1 1 := Rz (1/2)

/-- CNOT: Controlled-NOT gate.
    Copies control via Z-spider, XORs with target via X-spider. -/
def CNOT : ZxTerm 2 2 :=
  (Z 0 1 2 ⊗' id) ; (id ⊗' X 0 2 1)
