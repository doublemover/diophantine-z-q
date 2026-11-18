module
public import Mathlib.Tactic
public section
namespace DyadicMixedJacobianSanity318
/-- At (t,w)=(0,0), the arithmetic column detects the regular ramified
surface w²=2, even though the fibre derivative is zero. -/
theorem regular_ramified_column : ((-2:ℤ)-(-2)^2)/2 % 2 = 1 := by norm_num

theorem node_column : ((0:ℤ)-0^2)/2 % 2 = 0 := by norm_num

theorem trace_denominator : (16:ℤ)*2^4=256 := by norm_num
end DyadicMixedJacobianSanity318
