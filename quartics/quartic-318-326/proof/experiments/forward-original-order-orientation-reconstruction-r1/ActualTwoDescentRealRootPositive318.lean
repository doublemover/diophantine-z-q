module
public import ActualTwoDescentLocalCosetNonexceptional318
public section
noncomputable section
namespace ActualTwoDescentRealRootPositive318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentSimpleRootCoordinates318
open ActualTwoDescentKummerAffineCoordinates318 ActualTwoDescentRealKummerSigns318
open ActualTwoDescentKummerHom318 ActualTwoDescentSquareClassQuotient318

lemma actual_real_root_coordinate_positive (n : ℝ) (hn : 0 < n) (P : Point n) :
    0 < rootCoordinate (firstRoot n hn.ne') P := by
  cases P with
  | zero => exact zero_lt_one
  | some x y h =>
    by_cases hx : x= -3*n
    · subst x
      rw [actual_first_at_root]
      positivity
    · have hA : x+3*n ≠ 0 := by intro he; apply hx; linear_combination he
      rw [actual_first_coordinate n x y hn.ne' h hA]
      exact actual_real_first_positive n x y hn hA ((curve_equation n x y).mp h.left)

lemma actual_real_first_class_positive (n a b : ℝ) (hn : 0 < n) (ha : a ≠ 0) (hb : b ≠ 0)
    (P : Point n) (H : kummerClass n hn.ne' P=(classOf a ha,classOf b hb)) : 0 < a := by
  have he := congrArg Prod.fst H
  change classOf (rootCoordinate (firstRoot n hn.ne') P) _=classOf a ha at he
  obtain ⟨s,hs,hS⟩ := (class_of_eq_iff _ _ _ _).mp he
  have hp := actual_real_root_coordinate_positive n hn P
  rw [hS] at hp
  by_contra ha
  exact (not_le_of_gt hp) (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ha) (sq_nonneg s))

end ActualTwoDescentRealRootPositive318
