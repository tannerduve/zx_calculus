-- import ZxCalculus.DenotationalSemantics
-- import Mathlib.Data.Matrix.Kronecker

-- /-!
-- # Tensor Product Compatibility Lemmas

-- This file proves that our reindexed tensor product `tensLin` (which works with
-- `LinMap n m = Matrix (Fin (2^m)) (Fin (2^n)) ℂ`) is compatible with mathlib's
-- Kronecker product theory.

-- The key issue: mathlib's `⊗ₖ` produces matrices indexed by product types like
-- `Fin (2^n₁) × Fin (2^n₂)`, but we need indices `Fin (2^(n₁+n₂))`. The `tensLin`
-- definition uses `reindex` to convert between these, which breaks direct application
-- of mathlib lemmas.

-- This file bridges the gap by proving compatibility lemmas that let us:
-- 1. Apply mathlib's theorems to the underlying Kronecker product
-- 2. Handle the reindexing separately using mathlib's `reindex` lemmas

-- ## Main Results

-- * `tensLin_eq_reindex_kronecker`: Explicit connection between `tensLin` and `⊗ₖ`
-- * `tensLin_conjTranspose`: Conjugate transpose distributes over tensor product
-- * `tensLin_assoc_exists`: Associativity via mathlib's `kronecker_assoc`

-- ## Note

-- Many proofs require careful handling of equivalences between product types and flat Fin types.
-- These are left as `sorry` for now but can be completed using mathlib's equivalence machinery.
-- -/

-- open Matrix Complex
-- open scoped Kronecker Zx

-- noncomputable section

-- /-! ### Basic reindexing lemmas -/

-- /-- The equivalence used in tensLin for row indices -/
-- def tensLinRowEquiv (n₁ n₂ : ℕ) : Fin (2^(n₁ + n₂)) ≃ (Fin (2^n₁) × Fin (2^n₂)) :=
--   (Equiv.cast (by ring_nf)).trans finProdFinEquiv.symm

-- /-- The equivalence used in tensLin for column indices -/
-- def tensLinColEquiv (m₁ m₂ : ℕ) : Fin (2^(m₁ + m₂)) ≃ (Fin (2^m₁) × Fin (2^m₂)) :=
--   (Equiv.cast (by ring_nf)).trans finProdFinEquiv.symm

-- /-- Explicit form of tensLin in terms of reindex and kronecker -/
-- lemma tensLin_eq_reindex_kronecker {n₁ m₁ n₂ m₂ : ℕ}
--     (A : LinMap n₁ m₁) (B : LinMap n₂ m₂) :
--     A ⊗ₗ B = Matrix.reindex
--       (tensLinRowEquiv m₁ m₂).symm
--       (tensLinColEquiv n₁ n₂).symm
--       (A ⊗ₖ B) := by
--   rfl

-- /-! ### Kronecker product compatibility -/

-- /-- Kronecker product preserves conjugate transpose -/
-- lemma kronecker_conjTranspose {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
--     (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
--     (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
--   ext ⟨i, j⟩ ⟨k, l⟩
--   simp only [kronecker_apply, conjTranspose_apply, star_mul']

-- /-- tensLin preserves conjugate transpose -/
-- lemma tensLin_conjTranspose {n₁ m₁ n₂ m₂ : ℕ}
--     (A : LinMap n₁ m₁) (B : LinMap n₂ m₂) :
--     (A ⊗ₗ B)ᴴ = Aᴴ ⊗ₗ Bᴴ := by
--   ext i j
--   simp only [tensLin_eq_reindex_kronecker, conjTranspose_apply, Matrix.reindex_apply,
--              Matrix.submatrix_apply, kronecker_apply, star_mul']
--   -- Requires showing row/col equivalences swap correctly with conjugate transpose
--   sorry

-- /-! ### Associativity -/

-- /-- tensLin is associative (matches linMapAssoc)

--     This follows from mathlib's Matrix.kronecker_assoc' but requires
--     careful handling of equivalence composition between different
--     representations of (n₁ + n₂) + n₃ vs n₁ + (n₂ + n₃).
-- -/
-- lemma tensLin_assoc_clean {n₁ m₁ n₂ m₂ n₃ m₃ : ℕ}
--     (A : LinMap n₁ m₁) (B : LinMap n₂ m₂) (C : LinMap n₃ m₃) :
--     (A ⊗ₗ B) ⊗ₗ C = linMapAssoc (A ⊗ₗ (B ⊗ₗ C)) := by
--   sorry

-- /-! ### Identity properties -/

-- /-- Right identity for tensor product (alternative proof) -/
-- lemma tensLin_empty_right_alt {n m : ℕ} (A : LinMap n m) :
--     A ⊗ₗ (1 : LinMap 0 0) = A := by
--   sorry -- Requires careful handling of n + 0 = n and Fin (2^n) × Fin 1 ≃ Fin (2^n)

-- /-! ### Interaction with matrix multiplication -/
