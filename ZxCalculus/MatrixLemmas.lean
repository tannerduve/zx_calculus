import ZxCalculus.DenotationalSemantics
import ZxCalculus.RewriteTerm
import Mathlib.Data.Matrix.Kronecker

/-!
# Matrix Lemmas for ZX-Calculus

This file contains helper lemmas for proving soundness of ZX-calculus rewrite rules.
In particular, it focuses on:
- Properties of Hadamard conjugation
- Tensor products of basis states
- Interaction between Kronecker products and matrix operations

## Main Results

* `hadamard_ket0`: H|0⟩ = |+⟩
* `hadamard_ket1`: H|1⟩ = |-⟩
* `pow_tens_hadamard_ket0`: (H^⊗n)|0⟩^⊗n = |+⟩^⊗n
* `pow_tens_hadamard_ket1`: (H^⊗n)|1⟩^⊗n = |-⟩^⊗n
* `tensor_pow_interp`: Interpretation of tensor_pow as iterated Kronecker product
-/

open Matrix Complex Real ZxTerm
open scoped Zx

noncomputable section

/-! ### Dagger properties -/

/-- Helper: conjugate of phase exponential for Z-spider dagger -/
lemma dagger_Z_phase (α : ℚ) :
    Complex.exp (Complex.I * ↑(↑(-α) * Real.pi)) =
    star (Complex.exp (Complex.I * ↑(↑α * Real.pi))) := by
  sorry

/-- Helper: conjugate of phase exponential for X-spider dagger -/
lemma dagger_X_phase (α : ℚ) :
    Complex.exp (Complex.I * ↑(↑(-α) * Real.pi)) =
    star (Complex.exp (Complex.I * ↑(↑α * Real.pi))) := by sorry

/--
The dagger operation † on ZX diagrams is the graphical adjoint operator.

Formally: For a ZX diagram d representing a linear map A : ℂ^(2^n) → ℂ^(2^m),
the dagger d† represents the adjoint map A† : ℂ^(2^m) → ℂ^(2^n) satisfying
⟨Ax, y⟩ = ⟨x, A†y⟩ for all x, y.
-/
theorem dagger_adjoint_property {n m : ℕ} (d : ZxTerm n m) :
  interp (d†) = (interp d)ᴴ := by
  induction d
  · case gen k l g =>
    simp only [dagger, interp]
    induction g
    · case empty =>
      simp only [Nat.pow_zero, interp, interpGen]; simp
    · case id =>
      simp only [Nat.reducePow, interp, interpGen]; simp
    · case swap i j =>
      simp only [interp, interpGen, swap_gen]; aesop
    · case H =>
      simp only [Nat.reducePow, interp, interpGen, ketPlus, bra0, ketMinus, bra1,
      ket0, ket1, basisVector]
      -- Need to show Hadamard matrix is self-adjoint
      ext i j
      fin_cases i <;> fin_cases j <;> {
        simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
                   Matrix.sub_apply, Matrix.of_apply, Finset.sum_fin_eq_sum_range,
                   Finset.sum_range_one, Fin.zero_eta]
        norm_num
      }
    · case Z α i j =>
      simp only [interp, interpGen]
      -- Conjugate transpose distributes over addition and scalar multiplication
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
      -- Use outer product adjoint property: (|a⟩⟨b|)ᴴ = |b⟩⟨a|
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      -- Simplify the phase: star(e^(iαπ)) = e^(-iαπ)
      congr 1
      rw [dagger_Z_phase]
    · case X α i j =>
      simp only [interp, interpGen]
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      congr 1
      rw [dagger_X_phase]
    · case cup =>
      simp only [interp, interpGen]; aesop
    · case cap =>
      simp only [interp, interpGen, ket00, bra00, ket11, bra11, basisVector];
      aesop
  · case comp i j k A B ih₁ ih₂ =>
    simp only [dagger, interp, conjTranspose_mul]
    rw [← ih₁, ← ih₂]
  · case tens n₁ m₁ n₂ m₂ A B ih₁ ih₂ =>
    simp only [dagger, interp, ih₁, ih₂, tensLin]; aesop

/-! ### Basic Hadamard Properties -/

/-- The Hadamard gate maps |0⟩ to |+⟩ -/
lemma hadamard_ket0 : hadamardMatrix * ket0 = ketPlus := hadamard_zero_to_plus

/-- The Hadamard gate maps |1⟩ to |-⟩ -/
lemma hadamard_ket1 : hadamardMatrix * ket1 = ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp only [hadamardMatrix, ket1, ketMinus, ket0, basisVector, Matrix.mul_apply,
               Matrix.of_apply, Matrix.sub_apply, Fin.sum_univ_two]
    norm_num
  }

/-- The Hadamard gate is equal to the generator interpretation -/
lemma hadamard_eq_interpGen : hadamardMatrix = interpGen Generator.H := by
  rw [interpGen]
  exact hadamard_outer_product.symm

/-- Conjugate transpose of Hadamard times Hadamard is proportional to identity -/
lemma hadamard_adjoint_mul_hadamard :
    hadamardMatrixᴴ * hadamardMatrix = 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [hadamardMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two, star_one]
    norm_num
  }

/-! ### Outer Product Properties -/

/-- Multiplication of outer products: (|a⟩⟨b|) * (|c⟩⟨d|) = ⟨b|c⟩ • (|a⟩⟨d|) -/
lemma outer_product_mul {n m k : ℕ} (a : Qubits n) (b : Qubits m) (c : Qubits m) (d : Qubits k) :
    (a * bᴴ) * (c * dᴴ) = ((bᴴ * c) 0 0) • (a * dᴴ) := by
  sorry

/-- Conjugate transpose distributes over outer products -/
lemma outer_product_adjoint {n m : ℕ} (a : Qubits n) (b : Qubits m) :
    (a * bᴴ)ᴴ = b * aᴴ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
  rw [star_sum]
  congr 1
  ext k
  simp [mul_comm, Matrix.star_mul]

/-! ### Tensor Product (pow_tens) Properties -/

/-- Tensor product of |0⟩ with itself n times gives |0...0⟩ -/
@[simp] lemma pow_tens_ket0_eq_basis (n : ℕ) : pow_tens ket0 n = basisVector n 0 := by
  induction n
  · case zero =>
    simp [pow_tens]
  · case succ n ih =>
    by_cases h : n = 0
    · rw [h]
      simp only [Nat.reduceAdd, pow_tens, Fin.isValue, ket0]
    · simp only [pow_tens]
      rw [ih]
      -- Now prove the Kronecker product of basis vectors at 0 gives basis vector at 0
      ext i j
      simp only [basisVector, ket0, Matrix.of_apply]
       -- j = 0 (column vector), so we just need to show the entry depends on whether i = 0
      let i_split := finProdFinEquiv.symm (i.cast (by rw [pow_succ, mul_comm]))
       -- i_split.1 is the "ket0 component", i_split.2 is the "basisVector n 0 component"
       -- Both are 0 iff i = 0 in the product space
      by_cases hi : i = 0
      · -- i = 0 case: should be 1
        subst hi
        simp [i_split]
        split_ifs with h₁ h₂
        · rfl
        · exfalso
          apply h₂
          simp [Fin.divNat]
        · exfalso
          apply h₁
          simp [Fin.modNat]
      · -- i ≠ 0 case: should be 0
        simp [i_split]
        split_ifs with h₁ h₂
        · rfl
        · exfalso
          apply hi
          simp [Fin.divNat, Fin.modNat] at h₁ h₂
          ext
          -- h₁: i is divisible by 2^n, h₂: i < 2^n
          -- Only multiple of 2^n less than 2^n is 0
          have hdvd : 2^n ∣ (i : ℕ) := Nat.dvd_of_mod_eq_zero h₁
          -- If 2^n divides i and i < 2^n, then i = 0
          obtain ⟨k, hk⟩ := hdvd
          have hk_zero : k = 0 := by
            by_contra hk_ne
            have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
            have : (i : ℕ) ≥ 2^n := by
              calc (i : ℕ) = 2^n * k := hk
                _ ≥ 2^n * 1 := Nat.mul_le_mul_left _ hk_pos
                _ = 2^n := by ring
            -- This contradicts h₂
            omega
          rw [hk_zero, mul_zero] at hk
          simp [hk]
        all_goals {(try exfalso; omega); (try rfl)}

/-- Tensor product of |1⟩ with itself n times gives |1...1⟩ -/
lemma pow_tens_ket1_eq_basis (n : ℕ) : pow_tens ket1 n = basisVector n (2^n - 1) := by
  sorry

/-- |+⟩ as sum of basis states -/
lemma ketPlus_def : ketPlus = ket0 + ket1 := rfl

/-- |-⟩ as difference of basis states -/
lemma ketMinus_def : ketMinus = ket0 - ket1 := rfl


/-! ### tensor_pow Interpretation -/

/-- Interpretation of tensor_pow distributes over iterTens -/
lemma tensor_pow_interp {n m : ℕ} (d : ZxTerm n m) (k : ℕ) :
    interp (tensor_pow d k) = iterTens (interp d) k := by
  induction k with
  | zero => sorry
  | succ k ih => sorry

/-- Specific case: interpretation of tensor_pow H n -/
lemma tensor_pow_H_interp (n : ℕ) :
    interp (tensor_pow H n) = iterTens hadamardMatrix n := by
  rw [tensor_pow_interp]
  simp [H, interp, interpGen, hadamard_eq_interpGen]

/-! ### Phase Exponential Properties -/

/-- exp(i * π) = -1 -/
@[simp] lemma exp_I_pi : Complex.exp (Complex.I * ↑Real.pi) = -1 := by
  rw [mul_comm]
  exact Complex.exp_pi_mul_I

/-- exp(i * α * π + i * 2 * π) = exp(i * α * π) -/
@[simp] lemma exp_phase_add_two (α : ℚ) :
    Complex.exp (Complex.I * ((↑α + 2) * ↑Real.pi)) =
    Complex.exp (Complex.I * (↑α * ↑Real.pi)) := by
  have h1 : Complex.I * ((↑α + 2) * ↑Real.pi) =
      Complex.I * (↑α * ↑Real.pi) + Complex.I * (2 * ↑Real.pi) := by ring
  rw [h1, Complex.exp_add]
  have h2 : Complex.I * (2 * ↑Real.pi) = 2 * ↑Real.pi * Complex.I := by ring
  simp only [h2, Complex.exp_two_pi_mul_I, mul_one]

/-! ### Conjugate Transpose Properties -/

/-- Conjugate transpose of scalar multiple -/
lemma conjTranspose_smul {idx₁ idx₂ : Type*} (c : ℂ) (A : Matrix idx₁ idx₂ ℂ) :
    (c • A)ᴴ = star c • Aᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.star_mul]

/-- Conjugate transpose of sum -/
lemma conjTranspose_add {idx₁ idx₂ : Type*} (A B : Matrix idx₁ idx₂ ℂ) :
    (A + B)ᴴ = Aᴴ + Bᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.add_apply]

/-! ### Pi Copy Helper Definitions -/

/-- Cast X 1 1 1 ⊗ tensor_pow id k to the right type for composition -/
def x_pi_id_tens (k : ℕ) : ZxTerm (1 + k) (1 + k) :=
  by simpa [Nat.mul_one] using ((X 1 1 1).tens (tensor_pow id k))

/-- Cast Z 1 1 1 ⊗ tensor_pow id k to the right type for composition -/
def z_pi_id_tens (k : ℕ) : ZxTerm (1 + k) (1 + k) :=
  by simpa [Nat.mul_one] using ((Z 1 1 1).tens (tensor_pow id k))

/-- Cast tensor_pow (X 1 1 1) n to the right type for composition -/
def x_pi_pow (n : ℕ) : ZxTerm n n :=
  by simpa [Nat.mul_one] using (tensor_pow (X 1 1 1) n)

/-- Cast tensor_pow (Z 1 1 1) n to the right type for composition -/
def z_pi_pow (n : ℕ) : ZxTerm n n :=
  by simpa [Nat.mul_one] using (tensor_pow (Z 1 1 1) n)

end
