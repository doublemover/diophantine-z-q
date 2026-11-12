module
public import ActualTwoDescentTwoAdicEvenCoordinates318
public section
noncomputable section
namespace ActualTwoDescentRealKummerSigns318
set_option maxHeartbeats 16000000

/-- The first ORIGINAL Kummer coordinate is positive for every actual
non-two-torsion real point on the positive twist. -/
theorem actual_real_first_positive (n x y : ℝ) (hn : 0<n)
    (hA : x+3*n ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) : 0<x+3*n := by
  by_contra h
  have hneg : x+3*n<0 := lt_of_le_of_ne (le_of_not_gt h) hA
  have hx : x<0 := by linarith
  have hB : x-n<0 := by linarith
  have hp := mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hx hB) hneg
  nlinarith [sq_nonneg y]

/-- The exact two real components, retaining the signs of the original
second coordinate. No arbitrary sign convention is imposed. -/
theorem actual_real_components (n x y : ℝ) (hn : 0<n)
    (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    (n<x ∧ 0<x-n) ∨ (-3*n<x ∧ x<0 ∧ x-n<0) := by
  have hp := actual_real_first_positive n x y hn hA hc
  by_cases h : 0<x
  · left
    have hb : 0<x-n := by
      by_contra hb
      have hbneg : x-n<0 := lt_of_le_of_ne (le_of_not_gt hb) hB
      have hprod := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h hbneg) hp
      nlinarith [sq_nonneg y]
    exact ⟨by linarith,hb⟩
  · right
    have hxn : x<0 := lt_of_le_of_ne (le_of_not_gt h) hx
    exact ⟨by linarith,hxn,by linarith⟩

end ActualTwoDescentRealKummerSigns318
