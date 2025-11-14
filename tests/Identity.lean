import ZxCalculus.RewriteTerm

/-!
# Identity Tests

Tests for identity rules in ZX-calculus.
-/

open ZxTerm Real

/-- Z-spider with zero phase is identity -/
theorem z_zero_is_id : ZxEquiv (Z 0 1 1) id :=
  ZxEquiv.z_id

#check z_zero_is_id
