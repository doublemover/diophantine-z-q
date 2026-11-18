module
public import Mathlib.Tactic
public section
namespace RamifiedThreeClusterCharts318
variable {F : Type*} [Field F] [CharZero F]

/-- Scaling by a ramified coefficient uniformizer leaves the two closest
roots a unit times ρ² apart, not a unit times ρ apart. -/
theorem scaled_coefficients (rho u v w : F) (hr : rho^2 = 3)
    (hv : v^2-u^2 = -76800) (hw : w^2-u^2 = 375) :
    (v/rho)^2-(u/rho)^2 = -25600 ∧
    (w/rho)^2-(u/rho)^2 = 125 ∧
    (w/rho)^2-(v/rho)^2 = 8575*rho^2 := by
  have hn : rho ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  simp only [div_pow, hr]
  constructor
  · linear_combination (1/3:F)*hv
  constructor
  · linear_combination (1/3:F)*hw
  · linear_combination (1/3:F)*(hw-hv)

theorem split_node (W V rho : F) (hf : W^2-V^2=8575*rho^2) :
    (W-V)*((W+V)/8575)=rho^2 := by
  linear_combination (1/8575:F)*hf

end RamifiedThreeClusterCharts318
