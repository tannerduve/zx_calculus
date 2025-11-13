import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Complex.Basic
import ZxCalculus.AST

/-!
# Denotational Semantics for ZX-Calculus

This file defines the interpretation of ZX diagrams as linear maps between finite-dimensional
Hilbert spaces, represented concretely as complex matrices.

## Main Definitions

* `Qubits n`: The Hilbert space of n qubits (2^n-dimensional column vectors)
* `LinMap n m`: Linear maps from n qubits to m qubits (matrices)
* `basisVector n i`: The i-th computational basis state |i⟩ for n qubits
* `interpGen`: Interprets primitive ZX generators as matrices
* `interp`: Recursively interprets composite ZX diagrams as matrices

## Notation

* `ket0`, `ket1`: Computational basis states |0⟩, |1⟩
* `ketPlus`, `ketMinus`: Hadamard basis states |+⟩ = |0⟩+|1⟩, |-⟩ = |0⟩-|1⟩
* `bra0`, `bra1`: Dual computational basis states ⟨0|, ⟨1|
* `braPlus`, `braMinus`: Dual Hadamard basis states ⟨+|, ⟨-|
* `Aᴴ`: Conjugate transpose (adjoint) of matrix A
-/

open Matrix Complex Real

/--
The Hilbert space of n qubits, represented as 2^n-dimensional column vectors over ℂ.

This is concretely `Matrix (Fin (2^n)) (Fin 1) ℂ`, representing quantum states as column vectors.
-/
abbrev Qubits (n : ℕ) := Matrix (Fin (2^n)) (Fin 1) ℂ

/--
Linear maps between qubit spaces, represented as matrices over ℂ.

A `LinMap n m` is a matrix mapping n-qubit states to m-qubit states.
The type is `Matrix (Fin (2^m)) (Fin (2^n)) ℂ` - note the order matches function composition.
-/
abbrev LinMap (n m : ℕ) := Matrix (Fin (2^m)) (Fin (2^n)) ℂ

noncomputable section

/-! ### Basis States

Computational basis vectors and derived states.
-/

/--
The i-th computational basis vector |i⟩ for n qubits.

Returns a column vector with 1 in position i and 0 elsewhere.
-/
def basisVector (n : ℕ) (i : Fin (2 ^ n)) : Qubits n :=
  Matrix.of fun j _ => if i = j then 1 else 0

/--
Tensor a single-qubit state with itself n times: |ψ⟩^⊗n.

For example:
* `pow_tens ket0 3` gives |0⟩⊗|0⟩⊗|0⟩ = |000⟩
* `pow_tens ket1 2` gives |1⟩⊗|1⟩ = |11⟩
-/
def pow_tens (v : Qubits 1) : (n : ℕ) → Qubits n
  | 0 => basisVector 0 0  -- Empty state (1×1 identity)
  | 1 => v
  | n+1 =>
      -- Kronecker product, then reindex from (Fin 2 × Fin 2^n) to Fin 2^(n+1)
      Matrix.of fun i _ =>
        let i_split := finProdFinEquiv.symm (i.cast (by ring))
        kronecker v (pow_tens v n) i_split 0

@[simp] lemma pow_tens_zero (v : Qubits 1) : pow_tens v 0 = basisVector 0 0 := rfl
@[simp] lemma pow_tens_one (v : Qubits 1) : pow_tens v 1 = v := rfl

/-! #### Computational Basis (Z-basis)

The standard |0⟩, |1⟩ basis and multi-qubit tensor products.
-/

/-- Single-qubit computational basis state |0⟩ = [1, 0]ᵀ -/
def ket0 : Qubits 1 := basisVector 1 0

/-- Single-qubit computational basis state |1⟩ = [0, 1]ᵀ -/
def ket1 : Qubits 1 := basisVector 1 1

/-- Two-qubit basis state |00⟩ = |0⟩ ⊗ |0⟩ = [1, 0, 0, 0]ᵀ -/
def ket00 : Qubits 2 := basisVector 2 0

/-- Two-qubit basis state |01⟩ = |0⟩ ⊗ |1⟩ = [0, 1, 0, 0]ᵀ -/
def ket01 : Qubits 2 := basisVector 2 1

/-- Two-qubit basis state |10⟩ = |1⟩ ⊗ |0⟩ = [0, 0, 1, 0]ᵀ -/
def ket10 : Qubits 2 := basisVector 2 2

/-- Two-qubit basis state |11⟩ = |1⟩ ⊗ |1⟩ = [0, 0, 0, 1]ᵀ -/
def ket11 : Qubits 2 := basisVector 2 3

/-! #### Hadamard Basis (X-basis)

The |+⟩, |-⟩ eigenstates of the Pauli X operator.
-/

/--
X-basis state |+⟩ = |0⟩ + |1⟩ = [1, 1]ᵀ.
-/
def ketPlus : Qubits 1 := ket0 + ket1

/--
X-basis state |-⟩ = |0⟩ - |1⟩ = [1, -1]ᵀ.
-/
def ketMinus : Qubits 1 := ket0 - ket1

/-! #### Dual States (Bras)

Conjugate transposes of kets, representing row vectors in the dual space.
-/

/-- Bra ⟨0| = [1, 0] -/
def bra0 : Matrix (Fin 1) (Fin (2^1)) ℂ := ket0ᴴ

/-- Bra ⟨1| = [0, 1] -/
def bra1 : Matrix (Fin 1) (Fin (2^1)) ℂ := ket1ᴴ

/-- Bra ⟨00| -/
def bra00 : Matrix (Fin 1) (Fin (2^2)) ℂ := ket00ᴴ

/-- Bra ⟨01| -/
def bra01 : Matrix (Fin 1) (Fin (2^2)) ℂ := ket01ᴴ

/-- Bra ⟨10| -/
def bra10 : Matrix (Fin 1) (Fin (2^2)) ℂ := ket10ᴴ

/-- Bra ⟨11| -/
def bra11 : Matrix (Fin 1) (Fin (2^2)) ℂ := ket11ᴴ

/-- Bra ⟨+| = [1, 1] -/
def braPlus : Matrix (Fin 1) (Fin (2^1)) ℂ := ketPlusᴴ

/-- Bra ⟨-| = [1, -1] -/
def braMinus : Matrix (Fin 1) (Fin (2^1)) ℂ := ketMinusᴴ

/-! ### Quantum Gates

Matrix representations of common quantum gates.
-/

/--
The Hadamard matrix: H = [[1, 1], [1, -1]].

Rotates between the Z-basis and X-basis:
* H|0⟩ = |+⟩ = |0⟩ + |1⟩
* H|1⟩ = |-⟩ = |0⟩ - |1⟩
-/
def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 1],
    ![1, -1]]

/-! ### Basic Properties

Lemmas establishing properties of basis states and quantum gates.
-/

/--
The Hadamard matrix can be expressed as an outer product expansion.

This shows H = |+⟩⟨0| + |-⟩⟨1|
-/
lemma hadamard_outer_product :
    ketPlus * bra0 + ketMinus * bra1 = hadamardMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ketPlus, ketMinus, bra0, bra1, ket0, ket1, basisVector, hadamardMatrix,
               Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.of_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_one,
               Fin.zero_eta, Fin.mk_one] <;>
    norm_num

/--
Computational basis states are orthogonal: ⟨0|1⟩ = 0.

More generally, ⟨i|j⟩ = δᵢⱼ for basis states.
-/
lemma basis_orthogonal : bra0 * ket1 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [bra0, ket0, ket1, basisVector, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.of_apply]
  norm_num

/--
Computational basis states are normalized: ⟨0|0⟩ = 1.

The inner product of a basis state with itself is 1 (represented as a 1×1 matrix).
-/
lemma basis_normalized_0 : bra0 * ket0 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  all_goals {
    simp only [bra0, ket0, basisVector, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.of_apply]
    norm_num
  }

/--
The Hadamard matrix is self-inverse up to a scalar: H² = 2I.
-/
lemma hadamard_self_inverse :
  hadamardMatrix * hadamardMatrix = 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  simp only [hadamardMatrix, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
               Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
               Fin.zero_eta, Fin.mk_one] <;>
  norm_num

/--
The Hadamard gate maps the computational |0⟩ to the |+⟩ state.

This demonstrates the basis change property: H|0⟩ = |+⟩ = |0⟩ + |1⟩.
-/
lemma hadamard_zero_to_plus : hadamardMatrix * ket0 = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp only [hadamardMatrix, ket0, ketPlus, basisVector, ket1, Matrix.mul_apply,
               Matrix.of_apply, Matrix.add_apply, Fin.sum_univ_two]
    norm_num
  }

/-! ### Interpretation Functions

The denotational semantics: mapping ZX diagrams to matrices.
-/

/--
The semantic interpretation of the swap generator for n and m qubits.

This is a linear map from (n+m)-qubit space to (m+n)-qubit space that exchanges
the order of the two subsystems:

    swap(|a⟩ₙ ⊗ |b⟩ₘ) = |b⟩ₘ ⊗ |a⟩ₙ
-/
def swap_gen (n m : ℕ) : LinMap (n + m) (m + n) :=
  Matrix.of fun (i : Fin (2^(m+n))) (j : Fin (2^(n+m))) =>
    let m_out := i.val / (2^n)
    let n_out := i.val % (2^n)
    let n_in := j.val / (2^m)
    let m_in := j.val % (2^m)
    if m_out = m_in && n_out = n_in then 1 else 0

/--
Interpret a primitive ZX generator as a matrix.

Each generator is mapped to its corresponding linear map:
* `empty`: 1×1 identity (scalar 1)
* `id`: 2×2 identity wire
* `swap n m`: Permutation matrix swapping n and m qubit subsystems
* `H`: Hadamard gate as |+⟩⟨0| + |-⟩⟨1|
* `Z α n m`: Z-spider |0⟩^⊗m ⟨0|^⊗n + e^(iαπ) |1⟩^⊗m ⟨1|^⊗n
* `X α n m`: X-spider |+⟩^⊗m ⟨+|^⊗n + e^(iαπ) |-⟩^⊗m ⟨-|^⊗n
* `cup`: Bell state |00⟩ + |11⟩
* `cap`: Bell effect ⟨00| + ⟨11|
-/
def interpGen {n m : ℕ} (g : Generator n m) : LinMap n m :=
  match g with
  | .empty => 1  -- 1×1 identity (scalar)
  | .id => 1     -- 2×2 identity wire
  | .swap n m => swap_gen n m
  | .H => ketPlus * bra0 + ketMinus * bra1  -- |+⟩⟨0| + |-⟩⟨1|
  | .Z α n m => -- Z spider with phase α*π (α is rational multiple of π)
    let phase := (α : ℝ) * π
    ((pow_tens ket0 m) * (pow_tens ket0 n)ᴴ) + (Complex.exp (Complex.I * phase) • ((pow_tens ket1 m) * (pow_tens ket1 n)ᴴ))
  | .X α n m => -- X spider with phase α*π (α is rational multiple of π)
    let phase := (α : ℝ) * π
    ((pow_tens ketPlus m) * (pow_tens ketPlus n)ᴴ) + (Complex.exp (Complex.I * phase) • ((pow_tens ketMinus m) * (pow_tens ketMinus n)ᴴ))
  | .cup => ket00 + ket11  -- Bell state (|00⟩ + |11⟩)
  | .cap => bra00 + bra11  -- Bell effect (⟨00| + ⟨11|)

open scoped Kronecker

/-- Kronecker on `LinMap`, reindexed to `LinMap (n₁+n₂) (m₁+m₂)`. -/
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

/-- Iterated tensor product of a linear map with itself k times -/
def iterTens {n m : ℕ} (A : LinMap n m) : (k : ℕ) → LinMap (k * n) (k * m)
  | 0 => by simpa [Nat.zero_mul] using (1 : LinMap 0 0)
  | 1 => by simpa [Nat.one_mul] using A
  | k + 1 => by simpa [Nat.succ_mul, Nat.add_comm] using (A ⊗ₗ iterTens A k)

/-- Cast LinMap n m to LinMap (0 + n) (0 + m) -/
def linMapAddZeroLeft {n m : ℕ} (A : LinMap n m) : LinMap (0 + n) (0 + m) :=
  by simpa [LinMap, Nat.zero_add] using A

@[simp] lemma linMapAddZeroLeft_unfold {n m : ℕ} (A : LinMap n m) (i j) :
  linMapAddZeroLeft A i j = A i j := by
  simp [linMapAddZeroLeft]
  sorry

@[simp] lemma tensLin_empty_left {n m} (A : LinMap n m) :
  ((1 : LinMap 0 0) ⊗ₗ A) = linMapAddZeroLeft A := by
  ext i j
  simp [tensLin, Matrix.reindex, Matrix.of_apply,
        Matrix.kronecker, Matrix.kroneckerMap, Nat.zero_add, Matrix.one_apply, linMapAddZeroLeft]
  sorry

@[simp] lemma tensLin_empty_right {n m} (A : LinMap n m) :
  (A ⊗ₗ (1 : LinMap 0 0)) = A := by
  ext i j
  simp [tensLin, Matrix.reindex, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap,
        Nat.add_zero]
  -- Since the identity matrix has 1s on the diagonal and 0s elsewhere, the only non-zero terms in the sum are when the indices match.
  simp [Matrix.one_apply, Fin.val_add, Fin.val_mul, Fin.ext_iff];
  -- Since the indices are just rearranged, the equality holds.
  congr
  all_goals generalize_proofs at *;
  · -- Since the Fin type is essentially a natural number with a bound, the division and modulo operations should just give the same result as the original Fin. So the equality should hold by definition.
    ext; simp [Fin.ext_iff, Fin.val_add, Fin.val_mul];
    congr! 1;
    · ring;
    · norm_num at *;
  · ext ; simp [ Fin.ext_iff, Fin.val_add, Fin.val_mul ];
    grind

/-- Cast LinMap (n₁ + n₂ + n₃) (m₁ + m₂ + m₃) between association forms -/
def linMapAssoc {n₁ m₁ n₂ m₂ n₃ m₃ : ℕ} (A : LinMap (n₁ + (n₂ + n₃)) (m₁ + (m₂ + m₃))) :
    LinMap (n₁ + n₂ + n₃) (m₁ + m₂ + m₃) :=
  by simpa [LinMap, add_assoc] using A

/-- The helper equals the explicit cast -/
@[simp] lemma linMapAssoc_eq_cast {n₁ m₁ n₂ m₂ n₃ m₃ : ℕ}
    (A : LinMap (n₁ + (n₂ + n₃)) (m₁ + (m₂ + m₃))) :
  linMapAssoc A = (Nat.add_assoc n₁ n₂ n₃ ▸ Nat.add_assoc m₁ m₂ m₃ ▸ A : LinMap (n₁ + n₂ + n₃) (m₁ + m₂ + m₃)) := by
  sorry

@[simp] lemma tensLin_assoc {n₁ m₁ n₂ m₂ n₃ m₃}
  (A : LinMap n₁ m₁) (B : LinMap n₂ m₂) (C : LinMap n₃ m₃) :
  ((A ⊗ₗ B) ⊗ₗ C) = linMapAssoc (A ⊗ₗ (B ⊗ₗ C)) := by
  ext i j
  simp [tensLin, Matrix.reindex, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap,
        Equiv.prodAssoc, linMapAssoc]
  sorry

/--
Recursively interpret a composite ZX diagram as a matrix.

* Generators are interpreted via `interpGen`
* Sequential composition (`;`) becomes matrix multiplication
* Parallel composition (`⊗`) becomes Kronecker product (tensor product)
-/
def interp {n m : ℕ} : ZxTerm n m → LinMap n m
  | .gen g => interpGen g
  | f ; g => interp g * interp f  -- Matrix multiplication (note order reversal)
  | f ⊗ g => interp f ⊗ₗ interp g
