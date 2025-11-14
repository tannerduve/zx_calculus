import ZxCalculus.RewriteTerm

/-!
# Z-Spider Fusion Tests

Tests for Z-spider fusion rules.
-/

open ZxTerm Real

/-- Z-spider fusion adds phases -/
theorem z_fusion : ZxEquiv (Z (1/2) 1 1 ; Z (1/2) 1 1) (Z 1 1 1) := by
  have h := ZxEquiv.z_fus (1/2) (1/2) (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  ring_nf
  exact ZxEquiv.refl _

#check z_fusion
