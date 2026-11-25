module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public section
noncomputable section

namespace OriginalR8WildNormAxisProduct318

open scoped BigOperators

variable {G B : Type*} [Fintype G] [CommMonoid B]

/-- Keep the exact unit on the *whole* norm axis, rather than treating
the reduced coordinate congruence as an equality upstairs. The units
come from branch preservation in the same normal completed node. -/
theorem norm_axis (X : B) (σ : G → B → B) (u : G → Bˣ)
    (h : ∀ s, σ s X = (u s : B) * X) :
    ∃ v : Bˣ, (∏ s, σ s X) = (v:B) * X ^ Fintype.card G := by
  classical
  refine ⟨∏ s, u s,?_⟩
  simp only [h,Finset.prod_mul_distrib,Units.coe_prod,Finset.prod_const,Finset.card_univ]

end OriginalR8WildNormAxisProduct318

#print axioms OriginalR8WildNormAxisProduct318.norm_axis
