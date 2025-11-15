import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.ForMathlib.Matrix
import ZxCalculus.AST
import Mathlib.Data.Matrix.Kronecker

/-!
# Denotational semantics for the ZX-calculus

This file interprets ZX diagrams with `n` inputs and `m` outputs as matrices
acting on \(2^n\)- and \(2^m\)-dimensional complex Hilbert spaces.  It uses the
`QuantumInfo` library for kets, bras and standard single–qubit gates, together
with Mathlib's matrix and Kronecker product infrastructure.

Multi–qubit systems are modelled as tensor powers of the single–qubit space,
and the basic ZX generators (spiders, swap, cup, cap, …) are given their usual
matrix semantics.
-/

open Matrix Complex Real
open Braket -- For ket/bra notation

noncomputable section

/-! ### Type definitions -/

/-- Linear maps between `n`-qubit and `m`-qubit spaces, written as matrices over `ℂ`. -/
abbrev LinMap (n m : ℕ) := Matrix (Fin (2^m)) (Fin (2^n)) ℂ

/-! ### Converting between kets and matrices -/

/-- Convert a Ket to a column vector (matrix representation) -/
def ketToVec {d : Type*} [Fintype d] (ψ : Ket d) : Matrix d (Fin 1) ℂ :=
  Matrix.of fun i _ => ψ i

/-- Convert a Bra to a row vector -/
def braToVec {d : Type*} [Fintype d] (ψ : Bra d) : Matrix (Fin 1) d ℂ :=
  Matrix.of fun _ j => ψ.vec j

/-! ### Basic single–qubit states -/

/-- Single–qubit state \`∣0⟩\` in the computational basis. -/
def ket0 : Ket (Fin 2) := Ket.basis 0

/-- Single–qubit state \`∣1⟩\` in the computational basis. -/
def ket1 : Ket (Fin 2) := Ket.basis 1

/-- As column vectors -/
def ket0_vec : Matrix (Fin 2) (Fin 1) ℂ := ketToVec ket0
def ket1_vec : Matrix (Fin 2) (Fin 1) ℂ := ketToVec ket1

/-- \`∣+⟩\`, the uniform superposition state. -/
def ketPlus : Ket (Fin 2) := Ket.normalize (fun _ => 1) ⟨0, by norm_num⟩

/-- \`∣-⟩\`, the orthogonal superposition state. -/
def ketMinus : Ket (Fin 2) :=
  Ket.normalize (fun i => if i = 0 then 1 else -1) ⟨0, by norm_num⟩

/-- As column vectors -/
def ketPlus_vec : Matrix (Fin 2) (Fin 1) ℂ := ketToVec ketPlus
def ketMinus_vec : Matrix (Fin 2) (Fin 1) ℂ := ketToVec ketMinus

/-! ### Tensor products for multi–qubit states -/

/-- Type-level function sending `n` to the type of an `n`-qubit system. -/
@[simp] def QubitSpace : ℕ → Type
  | 0 => Unit
  | 1 => Qubit
  | n + 2 => Qubit × QubitSpace (n + 1)

/-- `Fintype` instance for `QubitSpace`. -/
instance instFintypeQubitSpace : (n : ℕ) → Fintype (QubitSpace n)
  | 0 => show Fintype Unit from inferInstance
  | 1 => show Fintype Qubit from inferInstance
  | n + 2 => @instFintypeProd _ _ _ (instFintypeQubitSpace (n + 1))

/-- Tensor power \`∣ψ⟩^{⊗ n}\`. -/
def ket_pow (ψ : Ket Qubit) : (n : ℕ) → Ket (QubitSpace n)
  | 0 => Ket.basis ()
  | 1 => ψ
  | n + 2 => Ket.prod ψ (ket_pow ψ (n + 1))

/-- Equivalence between `QubitSpace n` and `Fin (2^n)`,
used to pass between product and flat indexing. -/
def qubitSpaceEquiv : (n : ℕ) → QubitSpace n ≃ Fin (2^n)
  | 0 => {
      toFun := fun _ => 0
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun i => Fin.eq_of_val_eq (by simp [Fin.val_zero])
    }
  | 1 => Equiv.refl _
  | n + 2 =>
      let rec_equiv := qubitSpaceEquiv (n + 1)
      -- QubitSpace (n+2) = Qubit × QubitSpace (n+1) ≃ Fin 2 × Fin (2^(n+1)) ≃ Fin (2^(n+2))
      (Equiv.prodCongr (Equiv.refl Qubit) rec_equiv).trans
        (finProdFinEquiv.trans (Equiv.cast (by ring)))

/-- Convert a ket on `QubitSpace n` to a column vector with `Fin (2^n)` indexing. -/
def qubitSpaceToVec {n : ℕ} (ψ : Ket (QubitSpace n)) : Matrix (Fin (2^n)) (Fin 1) ℂ :=
  Matrix.of fun i _ => ψ.vec ((qubitSpaceEquiv n).symm i)

/-! ### Bell states -/

/-- Two–qubit basis state \`∣00⟩\`. -/
def ket00 : Ket (Fin 2 × Fin 2) := ket0 ⊗ ket0

/-- Two–qubit basis state \`∣11⟩\`. -/
def ket11 : Ket (Fin 2 × Fin 2) := ket1 ⊗ ket1

/-! ### Single–qubit gates -/

/-- Hadamard gate. -/
def H_gate : 𝐔[Fin 2] := Qubit.H

/-- Pauli `X` gate. -/
def X_gate : 𝐔[Fin 2] := Qubit.X

/-- Pauli `Z` gate. -/
def Z_gate : 𝐔[Fin 2] := Qubit.Z

/-- Extract the underlying matrix from a unitary. -/
def unitaryToMatrix {d : Type*} [Fintype d] [DecidableEq d] (U : 𝐔[d]) : Matrix d d ℂ :=
  U.val

/-- Controlled-NOT gate on two qubits.

The first qubit is the control and the second qubit is the target. -/
def CNOT_gate : 𝐔[Fin 2 × Fin 2] :=
  Qubit.controllize Qubit.X

/-- The matrix representation of CNOT is the standard 4×4 permutation matrix. -/
lemma CNOT_gate_matrix :
    Matrix.reindex finProdFinEquiv finProdFinEquiv CNOT_gate.val =
      ![![(1:ℂ), 0, 0, 0],
        ![0, 1, 0, 0],
        ![0, 0, 0, 1],
        ![0, 0, 1, 0]] := by
        ext i j
        simp only [CNOT_gate, Qubit.X, reindex_apply]
        fin_cases i <;> fin_cases j <;> rfl

/-! ### Spider operators -/

/-- Z-spider with phase `α * π`, with `n` inputs and `m` outputs.

Matrix: \`∣0⟩^{⊗ m} ⟨0∣^{⊗ n} + e^{i α π} ∣1⟩^{⊗ m} ⟨1∣^{⊗ n}\`. -/
def Z_spider (α : ℚ) (n m : ℕ) : LinMap n m :=
  let phase := (α : ℝ) * π
  -- Build |0⟩^⊗m and |1⟩^⊗m using ket_pow
  let ket0_m := ket_pow ket0 m
  let ket1_m := ket_pow ket1 m
  let ket0_n := ket_pow ket0 n
  let ket1_n := ket_pow ket1 n
  -- Convert to matrices with Fin (2^n) indexing
  let mat0_m := qubitSpaceToVec ket0_m
  let mat1_m := qubitSpaceToVec ket1_m
  let mat0_n := (qubitSpaceToVec ket0_n)ᴴ
  let mat1_n := (qubitSpaceToVec ket1_n)ᴴ
  -- Outer products: |0⟩^⊗m ⟨0|^⊗n + e^(iαπ) |1⟩^⊗m ⟨1|^⊗n
  mat0_m * mat0_n + (Complex.exp (Complex.I * phase) • (mat1_m * mat1_n))

/-- X-spider with phase `α * π`.

Matrix: \`∣+⟩^{⊗ m} ⟨+∣^{⊗ n} + e^{i α π} ∣-⟩^{⊗ m} ⟨-∣^{⊗ n}\`. -/
def X_spider (α : ℚ) (n m : ℕ) : LinMap n m :=
  let phase := (α : ℝ) * π
  let ketPlus_m := ket_pow ketPlus m
  let ketMinus_m := ket_pow ketMinus m
  let ketPlus_n := ket_pow ketPlus n
  let ketMinus_n := ket_pow ketMinus n
  let matPlus_m := qubitSpaceToVec ketPlus_m
  let matMinus_m := qubitSpaceToVec ketMinus_m
  let matPlus_n := (qubitSpaceToVec ketPlus_n)ᴴ
  let matMinus_n := (qubitSpaceToVec ketMinus_n)ᴴ
  matPlus_m * matPlus_n + (Complex.exp (Complex.I * phase) • (matMinus_m * matMinus_n))

/-! ### Swap Generator

The swap exchanges two subsystems: swap(|a⟩ₙ ⊗ |b⟩ₘ) = |b⟩ₘ ⊗ |a⟩ₙ

Equivalently: |00⟩⟨00| + |01⟩⟨10| + |10⟩⟨01| + |11⟩⟨11|
-/

def swap_matrix (n m : ℕ) : LinMap (n + m) (m + n) :=
  Matrix.of fun (i : Fin (2^(m+n))) (j : Fin (2^(n+m))) =>
    -- Decompose indices: i corresponds to output (m qubits then n qubits)
    --                    j corresponds to input (n qubits then m qubits)
    let m_out := i.val / (2^n)  -- First m qubits of output
    let n_out := i.val % (2^n)  -- Last n qubits of output
    let n_in := j.val / (2^m)   -- First n qubits of input
    let m_in := j.val % (2^m)   -- Last m qubits of input
    -- Swap connects input |n_in, m_in⟩ to output |m_in, n_in⟩
    if m_out = m_in && n_out = n_in then 1 else 0

/-! ### Generator Interpretation -/

/--
Interpret primitive ZX generators
-/
def interpGen {n m : ℕ} (g : Generator n m) : LinMap n m :=
  match g with
  | .empty => 1
  | .id => 1  -- Or use (unitaryToMatrix (1 : 𝐔[Fin 2]))
  | .swap n m => swap_matrix n m
  | .H => unitaryToMatrix H_gate
  | .Z α n m => Z_spider α n m
  | .X α n m => X_spider α n m
  | .cup =>
    -- Bell pair (|00⟩ + |11⟩) / √2
    let vec00 := ketToVec ket00
    let vec11 := ketToVec ket11
    Matrix.reindex finProdFinEquiv (Equiv.refl _) (vec00 + vec11)
  | .cap =>
    -- Bell measurement (⟨00| + ⟨11|) / √2
    let vec00 := ketToVec ket00
    let vec11 := ketToVec ket11
    Matrix.reindex (Equiv.refl _) finProdFinEquiv ((vec00 + vec11)ᴴ)

/-! ### Tensor Product for Linear Maps -/

open Kronecker

def tensLin {n₁ m₁ n₂ m₂}
  (A : LinMap n₁ m₁) (B : LinMap n₂ m₂) : LinMap (n₁ + n₂) (m₁ + m₂) :=
  Matrix.reindex
    (finProdFinEquiv.trans (Equiv.cast (by ring_nf)))
    (finProdFinEquiv.trans (Equiv.cast (by ring_nf)))
    (A ⊗ₖ B)

namespace ZxCalcNotation
scoped[Zx] infixl:70 " ⊗ₗ " => tensLin
end ZxCalcNotation
open scoped Zx

/-! ### Main Interpretation -/

/--
Interpret ZX diagrams as matrices, using QuantumInfo infrastructure.
-/
def interp {n m : ℕ} : ZxTerm n m → LinMap n m
  | .gen g => interpGen g
  | .comp f g => interp g * interp f
  | .tens f g => interp f ⊗ₗ interp g
