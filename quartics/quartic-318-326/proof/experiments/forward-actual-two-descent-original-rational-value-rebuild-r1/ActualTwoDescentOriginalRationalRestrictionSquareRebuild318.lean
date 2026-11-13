module
public import ActualTwoDescentOpenAdjointSectionsRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRationalRestrictionSquareRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentOriginalIdealOverlapValues318
variable {K : Type*} [Field K] [CharZero K]

/-- Restriction of the EXISTING global root ideal to the complete old overlap. -/
def restrictSection (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    (s : Γ(originalRootIdealSheaf n i,U)) : Γ(overlapIdeal n i,overlapEmbedding n ⁻¹ᵁ U) :=
  ActualTwoDescentOpenAdjointSectionsRebuild318.restrictSection (overlapEmbedding n)
    (originalRootIdealSheaf n i) U s

lemma coefficient_square (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    (s : Γ(originalRootIdealSheaf n i,U)) :
    (ActualTwoDescentOriginalGlobalRationalValueRebuild318.coefficientMap n i).app U s=
      (affineValue n i).app (overlapEmbedding n ⁻¹ᵁ U) (restrictSection n i U s) := by
  rw [←ActualTwoDescentOriginalOverlapRationalFrameRebuild318.adjoint]
  exact ActualTwoDescentOpenAdjointSectionsRebuild318.adjoint_apply _ _ _ _ U s

/-- Exact global/local rational-value identification, over EVERY nonempty
ambient open. This was not implied by the separate existence of the maps. -/
lemma value_square (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] :
    letI := ActualTwoDescentOpenRationalEvaluationRebuild318.preimage_nonempty (overlapEmbedding n) U
    ∀ s : Γ(originalRootIdealSheaf n i,U),
      ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U s=
        ActualTwoDescentOriginalOverlapRationalFrameRebuild318.value n i
          (overlapEmbedding n ⁻¹ᵁ U) (restrictSection n i U s) := by
  intro s
  change (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
    ((overlapScheme n).germToFunctionField _
      ((ActualTwoDescentOriginalGlobalRationalValueRebuild318.coefficientMap n i).app U s))=_
  rw [coefficient_square]
  rfl

/-- Equality of rational values is EXACTLY equality of native restrictions.
Global injectivity requires injectivity of this native restriction. -/
lemma eq_iff_section (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (s t : Γ(originalRootIdealSheaf n i,U)) :
    ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U s=
      ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U t ↔
        restrictSection n i U s=restrictSection n i U t := by
  letI := ActualTwoDescentOpenRationalEvaluationRebuild318.preimage_nonempty (overlapEmbedding n) U
  rw [value_square,value_square]
  exact (ActualTwoDescentOriginalOverlapRationalFrameRebuild318.injective n i _).eq_iff
end ActualTwoDescentOriginalRationalRestrictionSquareRebuild318
