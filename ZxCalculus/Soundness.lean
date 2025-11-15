import ZxCalculus.DenotationalSemantics
import ZxCalculus.RewriteTerm
import Mathlib.Data.Matrix.Mul

open scoped Zx

@[simp]
lemma interp_cast {n m n'} (h_n : n = n') (t : ZxTerm n m) :
  interp (h_n ▸ t) = h_n ▸ interp t := by
  subst h_n; rfl

@[simp] lemma interp_cast_congr {n n' m m'} (hn : n = n') (hm : m = m')
    (t : ZxTerm n m) :
  interp ((congr (congrArg ZxTerm hn) hm).mp t)
    = Eq.mp (by subst hn; subst hm; rfl) (interp t) := by
  subst hn; subst hm; rfl

/-! ### Helper definitions to hide casts -/

/-- Helper: cast Z spider from (n, m) to (n*1, m*1) for color change -/
def zCasted (α : ℚ) (n m : ℕ) : ZxTerm (n * 1) (m * 1) :=
  by simpa [Nat.add_zero] using ZxTerm.Z α n m

/-- Helper: cast X spider from (n, m) to (n*1, m*1) for color change -/
def xCasted (α : ℚ) (n m : ℕ) : ZxTerm (n * 1) (m * 1) :=
  by simpa [Nat.add_zero] using ZxTerm.X α n m

/-! ### Helper lemmas for soundness cases -/

lemma soundness_z_id :
    interp (ZxTerm.Z 0 1 1) = interp ZxTerm.id := by
  simp only [ZxTerm.Z, interp, interpGen, ZxTerm.id, Z_spider, qubitSpaceToVec]
  simp [ket_pow, qubitSpaceEquiv]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, ket0, ket1, Ket.basis]
  fin_cases i <;> fin_cases j <;> norm_num

lemma soundness_x_id :
    interp (ZxTerm.X 0 1 1) = interp ZxTerm.id := by
  simp only [ZxTerm.X, interp, interpGen, ZxTerm.id, X_spider, qubitSpaceToVec]
  simp [ket_pow, qubitSpaceEquiv]
  sorry

lemma soundness_color_change_Z (α : ℚ) (n m : ℕ) :
    interp (tensor_pow ZxTerm.H n ; zCasted α n m ; tensor_pow ZxTerm.H m)
    = interp (xCasted α n m) := by
  sorry

lemma soundness_color_change_X (α : ℚ) (n m : ℕ) :
    interp (tensor_pow ZxTerm.H n ; xCasted α n m ; tensor_pow ZxTerm.H m)
    = interp (zCasted α n m) := by
  sorry

/--
Soundness theorem: For any ZX diagrams `A` and `B`, if `A` and `B` are equivalent under the rewrite rules, then they represent the same matrix
-/
theorem soundness {n m : ℕ} (A B : ZxTerm n m) (equiv : ZxEquiv A B) : interp A = interp B := by
-- Proof by induction on the derivation that `A` and `B` are equivalent
    induction equiv
    rfl
    · case symm n m f g h₁ h₂ =>
        symm; exact h₂
    · case trans n m f g h h₁ h₂ ih₁ ih₂ =>
        rw [ih₁]; exact ih₂
    · case seq_cong n k m f₁ f₂ g₁ g₂ h₁ h₂ ih₁ ih₂ =>
        simp only [interp]; rw [ih₁, ih₂]
    · case tens_cong n₁ m₁ n₂ m₂ f₁ f₂ g₁ g₂ h₁ h₂ ih₁ ih₂ =>
        simp only [interp]; rw [ih₁, ih₂]
    · case assoc_comp n k l m f g h =>
        simp only [interp]; rw [Matrix.mul_assoc]
    · case assoc_tens n₁ m₁ n₂ m₂ n₃ m₃ f g h =>
        have hn : n₁ + n₂ + n₃ = n₁ + (n₂ + n₃) := by simp [add_assoc]
        have hm : m₁ + m₂ + m₃ = m₁ + (m₂ + m₃) := by simp [add_assoc]
        rw [interp_cast_congr hn hm]
        simp only [interp]
        sorry
    · case unit_comp_l f =>
        simp only [interp, ZxTerm.id, interpGen, mul_one]
    · case unit_comp_r f =>
        simp only [interp, ZxTerm.id, interpGen, one_mul]
    · case unit_tens_l n m f =>
        have hn : 0 + n = n := by simp
        have hm : 0 + m = m := by simp
        rw [interp_cast_congr hn hm]
        simp only [interp, ZxTerm.empty, interpGen]
        sorry
    · case unit_tens_r n m f =>
        have hn : n + 0 = n := by simp
        have hm : m + 0 = m := by simp
        rw [interp_cast_congr hn hm]
        simp only [Nat.add_zero, interp, tensLin, Nat.pow_zero, ZxTerm.empty, interpGen,
          Matrix.reindex_apply, eq_mp_eq_cast, cast_eq]
        sorry
    · case interchange => sorry
    · case z_fus n m k p q => sorry
    · case x_fus n m k p q => sorry
    · case z_id =>
        exact soundness_z_id
    · case x_id =>
        exact soundness_x_id
    · case color_change_Z α n m =>
        exact soundness_color_change_Z α n m
    · case color_change_X α n m =>
        exact soundness_color_change_X α n m
    · case z_pi_copy α => sorry
    · case x_pi_copy α => sorry
    · case z_phase_period α n m =>
        simp only [ZxTerm.Z, interp, interpGen, Z_spider]
        congr 1
        have h1 : ((α + 2 : ℚ) : ℝ) * Real.pi = (α : ℝ) * Real.pi + 2 * Real.pi := by
          push_cast; ring
        have h2 : Complex.I * ↑((α : ℝ) * Real.pi + 2 * Real.pi) =
                  Complex.I * ↑((α : ℝ) * Real.pi) + Complex.I * (2 * Real.pi) := by
          simp [Complex.ofReal_add]; ring
        rw [h1, h2, Complex.exp_add]
        have : Complex.exp (Complex.I * (2 * ↑Real.pi)) = 1 := by
          rw [mul_comm Complex.I, Complex.exp_two_pi_mul_I]
        rw [this]; simp
    · case x_phase_period α n m =>
        simp only [ZxTerm.X, interp, interpGen, X_spider]
        congr 1
        have h1 : ((α + 2 : ℚ) : ℝ) * Real.pi = (α : ℝ) * Real.pi + 2 * Real.pi := by
          push_cast; ring
        have h2 : Complex.I * ↑((α : ℝ) * Real.pi + 2 * Real.pi) =
                  Complex.I * ↑((α : ℝ) * Real.pi) + Complex.I * (2 * Real.pi) := by
          simp [Complex.ofReal_add]; ring
        rw [h1, h2, Complex.exp_add]
        have : Complex.exp (Complex.I * (2 * ↑Real.pi)) = 1 := by
          rw [mul_comm Complex.I, Complex.exp_two_pi_mul_I]
        rw [this]; simp
