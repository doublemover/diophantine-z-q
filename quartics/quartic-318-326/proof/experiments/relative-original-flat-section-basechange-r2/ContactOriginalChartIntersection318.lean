module
public import ContactOriginalRelativeOverlap318
public import SchemeOpenPushout318
public section
noncomputable section
namespace ContactOriginalChartIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "f" => ContactOriginalRelativePolynomialCharts318.finiteInto R c
local notation "g" => ContactOriginalRelativePolynomialCharts318.infinityInto R c
local notation "l" => ContactOriginalRelativeOverlap318.finiteEdge R c
local notation "r" => ContactOriginalRelativeOverlap318.infinityEdge R c
local notation "i" => ContactOriginalRelativeOverlap318.into R c
lemma square : l ≫ f=r ≫ g :=
  (ContactOriginalRelativeOverlap318.finiteEdge_into R c).trans
    (ContactOriginalRelativeOverlap318.infinityEdge_into R c).symm
lemma intersection : g ⁻¹ᵁ f.opensRange=r.opensRange := by
  ext y
  change (∃ x, f x=g y) ↔ ∃ z, r z=y
  constructor
  · rintro ⟨x,hx⟩
    have hy : g y∈i.opensRange := by
      rw [ContactOriginalRelativeOverlap318.full_intersection,
        ← ContactOriginalRelativePolynomialCharts318.finite_range,
        ← ContactOriginalRelativePolynomialCharts318.infinity_range]
      exact ⟨⟨x,hx⟩,⟨y,rfl⟩⟩
    obtain ⟨z,hz⟩ := hy
    refine ⟨z,g.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun k => k z) (ContactOriginalRelativeOverlap318.infinityEdge_into R c)).trans hz
  · rintro ⟨z,rfl⟩
    refine ⟨l z,?_⟩
    exact congrArg (fun k => k z) (square R c)
/-- The common Laurent ring is the whole actual finite/infinity chart
intersection of the original projective family, on arbitrary Q-algebras. -/
lemma cartesian : IsPullback l r f g :=
  IsOpenImmersion.isPullback l r f g (square R c).symm (intersection R c)
end ContactOriginalChartIntersection318
