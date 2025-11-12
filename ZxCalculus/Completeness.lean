import ZxCalculus.DenotationalSemantics
import ZxCalculus.RewriteTerm

/--
Soundness theorem: For any ZX diagrams `A` and `B`, if `A` and `B` are equivalent under the rewrite rules, then they represent the same matrix
-/
theorem soundness {n m : ℕ} (A B : ZxTerm n m) (equiv : ZxEquiv A B) : interp A = interp B := sorry


-- Will need to refine the following statements a bit
-- /--
-- Completeness theorem: For any ZX diagrams `A` and `B`, if `A` and `B` represent the same matrix, they are equivalent under the rewrite rules
-- -/
-- theorem completeness {n m : ℕ} (A B : ZxTerm n m) (equiv : interp A = interp B) : ZxEquiv A B := sorry

-- /--
-- Universality: In the Clifford+T fragment, for every matrix `A ∈ ℂ^{2^n} × C^{2^m}`, there exists a ZX diagram `D` such that `interp D = A`
-- -/
-- theorem universal {n m : ℕ} (A : LinMap n m) : ∃ D : ZxTerm n m, interp D = A := sorry
