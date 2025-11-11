import ZxCalculus.RewriteTerm
open ZxTerm Real

theorem z_fusion : ZxEquiv (Z (π/2) 1 1 ; Z (π/2) 1 1) (Z π 1 1) := by
  have h := ZxEquiv.z_fus (π/2) (π/2) (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  have : π/2 + π/2 = π := by ring
  rw [this]
  exact ZxEquiv.refl _

#check z_fusion

-- Need a soundness check next
