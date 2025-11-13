import ZxCalculus.DenotationalSemantics
import ZxCalculus.RewriteTerm
import Mathlib.Data.Matrix.Mul
import ZxCalculus.MatrixLemmas


@[simp]
lemma interp_cast {n m n'} (h_n : n = n') (t : ZxTerm n m) :
  interp (h_n ▸ t) = h_n ▸ interp t := by
  subst h_n; rfl

@[simp] lemma interp_cast_congr {n n' m m'} (hn : n = n') (hm : m = m')
    (t : ZxTerm n m) :
  interp ((congr (congrArg ZxTerm hn) hm).mp t)
    = Eq.mp (by subst hn; subst hm; rfl) (interp t) := by
  subst hn; subst hm; rfl

/--
Soundness theorem: For any ZX diagrams `A` and `B`, if `A` and `B` are equivalent under the rewrite rules, then they represent the same matrix
-/
theorem soundness {n m : ℕ} (A B : ZxTerm n m) (equiv : ZxEquiv A B) : interp A = interp B := by
-- Proof by induction on the derivation that `A` and `B` are equivalent
    induction equiv
    · case refl =>
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
        simp [interp]
    · case unit_comp_l f =>
        simp only [interp, ZxTerm.id, interpGen, mul_one]
    · case unit_comp_r f =>
        simp only [interp, ZxTerm.id, interpGen, one_mul]
    · case unit_tens_l n m f =>
        have hn : 0 + n = n := by simp
        have hm : 0 + m = m := by simp
        rw [interp_cast_congr hn hm]
        simp [interp, ZxTerm.empty, interpGen]
    · case unit_tens_r n m f =>
        have hn : n + 0 = n := by simp
        have hm : m + 0 = m := by simp
        rw [interp_cast_congr hn hm]
        simp [interp, ZxTerm.empty, interpGen]
    · case interchange => sorry
    · case z_fus n m k p q =>
        simp [interp, ZxTerm.Z, interpGen, Matrix.conjTranspose, Matrix.transpose]; ring_nf; sorry
    · case x_fus n m k p q =>
        simp [interp, ZxTerm.X, interpGen]; sorry
    · case z_id =>
        simp only [ZxTerm.Z, interp, interpGen, Nat.reducePow, pow_tens, ket0, basisVector,
          Fin.isValue, Rat.cast_zero, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          ket1, one_smul, ZxTerm.id]
        sorry
    · case x_id => sorry
    · case color_change_Z α n m =>
        simp only [ZxTerm.H, ZxTerm.Z]
        sorry
    · case color_change_X α n m =>
        simp only [ZxTerm.H, ZxTerm.X]
        sorry
    · case z_pi_copy α =>
        simp only [ZxTerm.X, ZxTerm.Z, interp, interpGen]
        sorry
    · case x_pi_copy α =>
        sorry
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
