import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import ZxCalculus.AST

open Matrix Complex Real

/-- The space of n qubits is represented as 2^n × 1 column vectors -/
abbrev Qubits (n : ℕ) := Matrix (Fin (2^n)) (Fin 1) ℂ

/-- Linear maps between qubit spaces are matrices -/
abbrev LinMap (n m : ℕ) := Matrix (Fin (2^m)) (Fin (2^n)) ℂ

noncomputable section

/-- The swap matrix for 2 qubits (4×4) -/
def swap_2x2 : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0, 0],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1]]

/-- General swap for n and m qubits -/
def swap_gen (n m : ℕ) : LinMap (n + m) (m + n) :=
  Matrix.of fun (i : Fin (2^(m+n))) (j : Fin (2^(n+m))) =>
    let m_out := i.val / (2^n)
    let n_out := i.val % (2^n)
    let n_in := j.val / (2^m)
    let m_in := j.val % (2^m)
    if m_out = m_in && n_out = n_in then 1 else 0

/-- General basis vector |i⟩ for n qubits -/
def basisVector (n : ℕ) (i : Fin (2 ^ n)) : Qubits n :=
  Matrix.of fun j _ => if i = j then 1 else 0

/-- Tensor a single-qubit state with itself n times: |ψ⟩^⊗n -/
def pow_tens (v : Qubits 1) : (n : ℕ) → Qubits n
  | 0 => basisVector 0 0  -- Empty state (1×1 identity)
  | 1 => v
  | n+1 =>
      let prev := pow_tens v n
      -- Kronecker product, then reindex from (Fin 2 × Fin 2^n) to Fin 2^(n+1)
      Matrix.of fun i _ =>
        let i_split := finProdFinEquiv.symm (i.cast (by ring))
        kronecker v prev i_split 0

/-- Single-qubit basis state |0⟩ = [1, 0]ᵀ -/
def ket0 : Qubits 1 := basisVector 1 0

/-- Single-qubit basis state |1⟩ = [0, 1]ᵀ -/
def ket1 : Qubits 1 := basisVector 1 1

/-- Two-qubit basis state |00⟩ = [1, 0, 0, 0]ᵀ -/
def ket00 : Qubits 2 := basisVector 2 0

/-- Two-qubit basis state |01⟩ = [0, 1, 0, 0]ᵀ -/
def ket01 : Qubits 2 := basisVector 2 1

/-- Two-qubit basis state |10⟩ = [0, 0, 1, 0]ᵀ -/
def ket10 : Qubits 2 := basisVector 2 2

/-- Two-qubit basis state |11⟩ = [0, 0, 0, 1]ᵀ -/
def ket11 : Qubits 2 := basisVector 2 3

/-- X-basis state |+⟩ = |0⟩ + |1⟩ = [1, 1]ᵀ -/
def ketPlus : Qubits 1 := ket0 + ket1

/-- X-basis state |-⟩ = |0⟩ - |1⟩ = [1, -1]ᵀ -/
def ketMinus : Qubits 1 := ket0 - ket1

/-- The Hadamard matrix as explicit entries -/
def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 1],
    ![1, -1]]

/-- Hadamard as outer product expansion equals explicit matrix -/
lemma hadamard_outer_product :
    ketPlus * ket0ᴴ + ketMinus * ket1ᴴ = hadamardMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ketPlus, ketMinus, ket0, ket1, basisVector, hadamardMatrix,
               Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.of_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_one,
               Fin.zero_eta, Fin.mk_one] <;>
    norm_num

/-- Computational basis states are orthogonal: ⟨0|1⟩ = 0 -/
lemma basis_orthogonal : ket0ᴴ * ket1 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [ket0, ket1, basisVector, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.of_apply]
  norm_num


/-- Computational basis states are normalized: ⟨0|0⟩ = 1 (scalar) -/
lemma basis_normalized_0 : ket0ᴴ * ket0 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  all_goals {
    simp only [ket0, basisVector, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.of_apply]
    norm_num
  }

/-- Hadamard is self-inverse: H² = 2I -/
lemma hadamard_self_inverse :
  hadamardMatrix * hadamardMatrix = 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  simp only [hadamardMatrix, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
               Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
               Fin.zero_eta, Fin.mk_one] <;>
  norm_num

/-- Hadamard maps |0⟩ to |+⟩ -/
lemma hadamard_zero_to_plus : hadamardMatrix * ket0 = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp only [hadamardMatrix, ket0, ketPlus, basisVector, ket1, Matrix.mul_apply,
               Matrix.of_apply, Matrix.add_apply, Fin.sum_univ_two]
    norm_num
  }

/-- Interpret ZX generators as matrices -/
def interpGen {n m : ℕ} (g : Generator n m) : LinMap n m :=
  match g with
  | .empty => 1  -- 1×1 identity
  | .id => 1     -- 2×2 identity
  | .swap n m => swap_gen n m
  | .H => ketPlus * ket0ᴴ + ketMinus * ket1ᴴ  -- |+⟩⟨0| + |-⟩⟨1|
  | .Z α n m => -- Z spider
    -- Convert rational coefficient to the angle it represents
    let phase := (α : ℝ) * π
    sorry
  | .X α n m => -- X spider
    -- Convert rational coefficient to the angle it represents
    let phase := (α : ℝ) * π
    sorry
  | .cup => ket00 + ket11  -- Bell state (|00⟩ + |11⟩)
  | .cap => ket00ᴴ + ket11ᴴ  -- Bell effect (⟨00| + ⟨11|)

/-- Interpret ZX diagrams as matrices -/
def interp {n m : ℕ} : ZxTerm n m → LinMap n m
  | .gen g => interpGen g
  | f ; g => interp g * interp f  -- Matrix multiplication
  | f ⊗ g =>
    Matrix.of fun i j =>
      let i_prod := finProdFinEquiv.symm (i.cast (by ring))
      let j_prod := finProdFinEquiv.symm (j.cast (by ring))
      kronecker (interp f) (interp g) i_prod j_prod
