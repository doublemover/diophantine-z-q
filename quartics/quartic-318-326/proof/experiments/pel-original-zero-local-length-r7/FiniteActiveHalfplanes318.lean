module
public import Mathlib
public section
noncomputable section
namespace FiniteActiveHalfplanes318
open Set
/-- Inactive inequalities remain strict on an actual open neighborhood.
This is the local cone mechanism, not a claim that any quotient is a manifold. -/
theorem local_active_constraints {ι X : Type*} [Finite ι] [TopologicalSpace X]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (c : ι → ℝ)
    (p : X) (hp : ∀ i, f i p ≤ c i) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, (∀ i, f i x ≤ c i) ↔ (∀ i, f i p = c i → f i x ≤ c i) := by
  classical
  let U : Set X := {x | ∀ i, f i p < c i → f i x < c i}
  have hopen : IsOpen U := by
    change IsOpen {x | ∀ i, f i p < c i → f i x < c i}
    change IsOpen (⋂ i, {x | f i p < c i → f i x < c i})
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : f i p < c i
    · simpa only [hi, true_implies] using isOpen_lt (hf i) continuous_const
    · simp [hi]
  refine ⟨U, hopen, (by intro i hi; exact hi), ?_⟩
  intro x hx
  constructor
  · intro h i _
    exact h i
  · intro h i
    rcases lt_or_eq_of_le (hp i) with hi | hi
    · exact le_of_lt (hx i hi)
    · exact h i hi
end FiniteActiveHalfplanes318
