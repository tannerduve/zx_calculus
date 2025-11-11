import ZxCalculus.RewriteTerm
open ZxTerm Real

/-- Hadamard conjugation converts Z to X -/
theorem hadamard_conjugates_z_to_x :
  ZxEquiv ((H ; Z (1/4) 1 1) ; H) (X (1/4) 1 1) := by
  exact ZxEquiv.color_change_Z (1/4) 1 1

/-- Hadamard conjugation converts X to Z -/
theorem hadamard_conjugates_x_to_z :
  ZxEquiv ((H ; X (1/3) 1 1) ; H) (Z (1/3) 1 1) := by
  exact ZxEquiv.color_change_X (1/3) 1 1

/-- Double Hadamard is identity (via color change) -/
theorem double_hadamard_via_color_change :
  ZxEquiv ((H ; H) ; Z 0 1 1) (Z 0 1 1) := by
  have h1 := ZxEquiv.color_change_Z 0 1 1
  have h2 : ZxEquiv ((H ; Z 0 1 1) ; H) (X 0 1 1) := h1
  have h3 := ZxEquiv.x_id
  have h4 : ZxEquiv (X 0 1 1) id := h3
  sorry -- Need to compose these properly

#check hadamard_conjugates_z_to_x
#check hadamard_conjugates_x_to_z
