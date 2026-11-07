module
public import HTail318
public section
namespace HCubic318
variable (p : ℕ) [Fact p.Prime]
theorem cubic_formula (w : ℚ_[p]) :
    HTail318.cubic p w = 1 + w/10 + w^2/24 + 5*w^3/208 := by
  norm_num [HTail318.cubic, HTail318.term, HCoefficients318.coefficient,
    Finset.sum_range_succ, show Nat.choose 4 2=6 by decide,
    show Nat.choose 6 3=20 by decide]
  ring
end HCubic318
#print axioms HCubic318.cubic_formula
