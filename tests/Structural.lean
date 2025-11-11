import ZxCalculus.RewriteTerm
open ZxTerm Real

/-- Composition is associative -/
theorem comp_assoc :
  ZxEquiv ((H ; Z 1 1 1) ; X (1/2) 1 1) (H ; (Z 1 1 1 ; X (1/2) 1 1)) := by
  exact ZxEquiv.assoc_comp H (Z 1 1 1) (X (1/2) 1 1)

/-- Identity is left unit -/
theorem id_left_unit :
  ZxEquiv (id ; H) H := by
  exact ZxEquiv.unit_comp_l H

/-- Identity is right unit -/
theorem id_right_unit :
  ZxEquiv (H ; id) H := by
  exact ZxEquiv.unit_comp_r H

/-- Tensor with empty is left unit -/
theorem empty_tens_left :
  ZxEquiv (by simpa [Nat.zero_add] using (empty.tens H)) H := by
  exact ZxEquiv.unit_tens_l H

/-- Tensor with empty is right unit -/
theorem empty_tens_right :
  ZxEquiv (by simpa [Nat.add_zero] using (H.tens empty)) H := by
  exact ZxEquiv.unit_tens_r H

/-- Interchange law example -/
theorem interchange_example :
  ZxEquiv ((H.tens id) ; (id.tens H)) ((H ; id).tens (id ; H)) := by
  exact ZxEquiv.interchange H id id H

/-- Tensor is associative -/
theorem tens_assoc :
  ZxEquiv
    (by simpa [Nat.add_assoc] using ((H.tens id).tens id))
    (by simpa [Nat.add_assoc] using (H.tens (id.tens id))) := by
  exact ZxEquiv.assoc_tens H id id

#check comp_assoc
#check id_left_unit
#check interchange_example
