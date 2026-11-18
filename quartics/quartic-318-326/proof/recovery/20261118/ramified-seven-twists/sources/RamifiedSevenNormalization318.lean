module
public import Mathlib.Tactic
public section
namespace RamifiedSevenNormalization318

/-- The new coordinate in the ramified generic field is integral by its monic
square relation. This field lemma does not invert U on an integral chart. -/
theorem middle_ratio {F : Type*} [Field F] (rho U h : F)
    (hU : U ≠ 0) (he : rho^2 = U^2*(h^2-1)) :
    (rho/U)^2 = h^2-1 ∧ U*(rho/U) = rho := by
  constructor
  · rw [div_pow, he]
    field_simp [hU] <;> ring
  · field_simp [hU] <;> ring

theorem terminal_ratio {F : Type*} [Field F] (rho W a : F)
    (hW : W ≠ 0) (he : rho^2 = W^2*(1-a^2)) :
    (rho/W)^2 = 1-a^2 ∧ W*(rho/W) = rho := by
  constructor
  · rw [div_pow, he]
    field_simp [hW] <;> ring
  · field_simp [hW] <;> ring

/-- Two middle-chart directions specialize to the split crossing when t=0. -/
theorem middle_ends {F : Type*} [Field F] (h : F) (hh : h^2-1=0) :
    h=1 ∨ h = -1 := by
  have hmul : (h-1)*(h+1)=0 := by linear_combination hh
  rcases mul_eq_zero.mp hmul with hz | hz
  · exact Or.inl (sub_eq_zero.mp hz)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hz)

end RamifiedSevenNormalization318
