module
public import ActualTwoDescentOriginalOverlapValueImageRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRationalImageBoundRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalRationalAdditiveImageRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Every actual global-section value is a regular value on the ENTIRE
intersection of the ambient open with the old common chart. -/
lemma regular_on_overlap (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] :
    letI := ActualTwoDescentOpenRationalEvaluationRebuild318.preimage_nonempty (overlapEmbedding n) U
    ∀ z : (originalCubicScheme n).functionField,z ∈ image n i U →
      ∃ a : Γ(overlapScheme n,overlapEmbedding n ⁻¹ᵁ U),
        ActualTwoDescentOriginalOverlapValueImageRebuild318.regularValue n
          (overlapEmbedding n ⁻¹ᵁ U) a=z := by
  intro z hz
  obtain ⟨s,hs⟩ := (mem_image n i U z).mp hz
  apply (ActualTwoDescentOriginalOverlapValueImageRebuild318.full_image n i _ z).mp
  refine ⟨ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.restrictSection n i U s,?_⟩
  rw [←ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.value_square]
  exact hs

/-- The remaining global injectivity obligation is exposed exactly,
not filled by an abstract isomorphism or new hypothesis in the main theorem. -/
lemma injective_iff_restriction (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] :
    Function.Injective (ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U) ↔
      Function.Injective (ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.restrictSection n i U) := by
  constructor
  · intro h s t hst
    exact h ((ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.eq_iff_section n i U s t).mpr hst)
  · intro h s t hst
    exact h ((ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.eq_iff_section n i U s t).mp hst)
end ActualTwoDescentOriginalRationalImageBoundRebuild318
