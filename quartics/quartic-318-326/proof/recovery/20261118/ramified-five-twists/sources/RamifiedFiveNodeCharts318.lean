module
public import Mathlib.Tactic
public section
namespace RamifiedFiveNodeCharts318

variable {F : Type*} [Field F] [CharZero F]

/-- In the first 5-direction chart the two branch variables multiply to 5. -/
theorem finite_node (w u : F) (h : w^2-u^2=15) :
    (w-u)*((w+u)/3) = 5 := by
  linear_combination (1/3:F)*h

theorem exchange (w u : F) :
    ((w-(-u))=3*((w+u)/3)) ∧ ((w+(-u))/3=(w-u)/3) := by
  constructor <;> ring

/-- On the resolved middle chart, fixed points of the branch-swapping
involution satisfy a quadratic, without treating division at zero as valid. -/
theorem swap_fixed {K : Type*} [Field K] (c x : K) (hx : x ≠ 0) :
    (-c)/x = x ↔ x^2 = -c := by
  rw [div_eq_iff hx, pow_two]
  exact eq_comm

/-- Relation for the invariant parameter z=πv in a fixed smooth chart. -/
theorem fixed_node (pi v : F) (h : pi^2=5) :
    (pi*v)^2 = 5*v^2 := by rw [mul_pow, h]

end RamifiedFiveNodeCharts318
