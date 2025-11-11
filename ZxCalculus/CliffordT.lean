import ZxCalculus.AST
import ZxCalculus.RewriteTerm

/-!
# Clifford+T Gates

Standard gates for fault-tolerant quantum computing.

* `T`: π/4 Z-rotation (non-Clifford, makes gate set universal)
* `S`: π/2 Z-rotation (Clifford gate, equals T²)
* `CNOT`: Controlled-NOT (Clifford gate)
-/

open ZxTerm

/-- T gate: π/4 Z-rotation. Non-Clifford gate required for universality. -/
def T : ZxTerm 1 1 := Z (1/4) 1 1

/-- S gate: π/2 Z-rotation. Clifford gate, equivalent to T². -/
def S : ZxTerm 1 1 := T ; T

/-- CNOT: Controlled-NOT gate.
    Copies control via Z-spider, XORs with target via X-spider. -/
def CNOT : ZxTerm 2 2 :=
  (Z 0 1 2 ⊗ id) ; (id ⊗ X 0 2 1)

-- Other clifford gates can go here
