module
public import Mathlib.Tactic
public section
namespace TameTwistFixedCharts318

/-- A bit records odd valuation of the corresponding twist scalar.
The finite root sheet labels are the three signs other than j. -/
theorem finite_fixed_iff (b : Fin 4 → Bool) (j : Fin 4) (hn : ∃ i, b i = true) :
    (∀ i, i ≠ j → b i = false) ↔
      (b j = true ∧ ∀ i, i ≠ j → b i = false) := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := hn
    have hij : i = j := by
      by_contra he
      rw [h i he] at hi
      cases hi
    exact ⟨hij ▸ hi, h⟩
  · exact And.right

/-- A reciprocal sign ratio is unchanged exactly when its two bits agree. -/
theorem infinity_fixed_iff (b : Fin 4 → Bool) (hn : ∃ i, b i = true) :
    (∀ i, b i = b 0) ↔ (∀ i, b i = true) := by
  constructor
  · intro h i
    obtain ⟨j, hj⟩ := hn
    exact (h i).trans ((h j).symm.trans hj)
  · intro h i
    exact (h i).trans (h 0).symm

variable {R : Type*} [CommRing R]

/-- The anti-invariant generator x and ramified uniformizer π give invariant
z=πx. No division or cancellation on a special-fibre chart is used. -/
theorem invariant_square (x pi t p : R) (hx : x^2 = t) (hp : pi^2 = p) :
    ((-pi)*(-x) = pi*x) ∧ (pi*x)^2 = p*t := by
  exact ⟨by ring, by rw [mul_pow, hp, hx]⟩

theorem node_chart_relations (p v : R) :
    (p*v)^2 = p*(p*v^2) ∧ (v*p)^2 = (p*v^2)*p := by
  constructor <;> ring

end TameTwistFixedCharts318
