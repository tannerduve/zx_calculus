import ZxCalculus.DenotationalSemantics
import ZxCalculus.RewriteTerm
import Mathlib.Data.Matrix.Mul
import ZxCalculus.MatrixLemmas

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

lemma soundness_assoc_tens {n₁ m₁ n₂ m₂ n₃ m₃ : ℕ}
    (f : ZxTerm n₁ m₁) (g : ZxTerm n₂ m₂) (h : ZxTerm n₃ m₃) :
    (interp f ⊗ₗ interp g) ⊗ₗ interp h = linMapAssoc (interp f ⊗ₗ (interp g ⊗ₗ interp h)) := by
  sorry

lemma soundness_unit_tens_l {n m : ℕ} (f : ZxTerm n m) :
    (1 : LinMap 0 0) ⊗ₗ interp f = linMapAddZeroLeft (interp f) := by
  sorry

lemma soundness_interchange {n₁ k₁ m₁ n₂ k₂ m₂ : ℕ}
    (f : ZxTerm n₁ k₁) (f' : ZxTerm k₁ m₁) (g : ZxTerm n₂ k₂) (g' : ZxTerm k₂ m₂) :
    interp ((f ⊗ g) ; (f' ⊗ g')) = interp ((f ; f') ⊗ (g ; g')) := by
  sorry

lemma soundness_z_fus {n m k : ℕ} (α β : ℚ) :
    interp (ZxTerm.Z α n m ; ZxTerm.Z β m k) = interp (ZxTerm.Z (α + β) n k) := by
  sorry

lemma soundness_x_fus {n m k : ℕ} (α β : ℚ) :
    interp (ZxTerm.X α n m ; ZxTerm.X β m k) = interp (ZxTerm.X (α + β) n k) := by
  sorry

lemma soundness_z_id :
    interp (ZxTerm.Z 0 1 1) = interp ZxTerm.id := by
  sorry

lemma soundness_x_id :
    interp (ZxTerm.X 0 1 1) = interp ZxTerm.id := by
  sorry

lemma soundness_color_change_Z (α : ℚ) (n m : ℕ) :
    interp (tensor_pow ZxTerm.H n ; zCasted α n m ; tensor_pow ZxTerm.H m)
    = interp (xCasted α n m) := by
  sorry

lemma soundness_color_change_X (α : ℚ) (n m : ℕ) :
    interp (tensor_pow ZxTerm.H n ; xCasted α n m ; tensor_pow ZxTerm.H m)
    = interp (zCasted α n m) := by
  sorry

lemma soundness_z_pi_copy {α : ℚ} {k n : ℕ} :
    interp (x_pi_id_tens k ; ZxTerm.Z α (1 + k) n) = interp (ZxTerm.Z (-α) (1 + k) n ; x_pi_pow n) := by
  sorry

lemma soundness_x_pi_copy (α : ℚ) (k n : ℕ) :
    interp (z_pi_id_tens k ; ZxTerm.X α (1 + k) n) = interp (ZxTerm.X (-α) (1 + k) n ; z_pi_pow n) := by
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
        simp [interp, ZxTerm.empty, interpGen]
    · case interchange => exact soundness_interchange _ _ _ _
    · case z_fus n m k p q =>
        exact soundness_z_fus p q
    · case x_fus n m k p q =>
        exact soundness_x_fus p q
    · case z_id =>
        exact soundness_z_id
    · case x_id =>
        exact soundness_x_id
    · case color_change_Z α n m =>
        exact soundness_color_change_Z α n m
    · case color_change_X α n m =>
        exact soundness_color_change_X α n m
    · case z_pi_copy α =>
        exact soundness_z_pi_copy
    · case x_pi_copy α =>
        exact soundness_x_pi_copy α _ _
    · case z_phase_period α n m =>
        simp [ZxTerm.Z, interp, interpGen]
    · case x_phase_period α n m =>
        simp [ZxTerm.X, interp, interpGen]

-- Will need to refine the following statements a bit
-- /--
-- Completeness theorem: For any ZX diagrams `A` and `B`, if `A` and `B` represent the same matrix, they are equivalent under the rewrite rules
-- -/
-- theorem completeness {n m : ℕ} (A B : ZxTerm n m) (equiv : interp A = interp B) : ZxEquiv A B := sorry

-- /--
-- Universality: In the Clifford+T fragment, for every matrix `A ∈ ℂ^{2^n} × C^{2^m}`, there exists a ZX diagram `D` such that `interp D = A`
-- -/
-- theorem universal {n m : ℕ} (A : LinMap n m) : ∃ D : ZxTerm n m, interp D = A := sorry
