module
public import ActualTwoDescentOriginalRationalAdditiveImageRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapValueImageRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalOverlapOldFrameComparison318
variable {K : Type*} [Field K] [CharZero K]

/-- The full regular-function image on ANY nonempty common-chart open,
viewed in the original global field via the actual generic-stalk map. -/
def regularValue (n : K) (U : (overlapScheme n).Opens) [Nonempty U] :
    Γ(overlapScheme n,U) →+* (originalCubicScheme n).functionField :=
  (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm.toRingHom.comp
    ((overlapScheme n).germToFunctionField U).hom

lemma regular_injective (n : K) (U : (overlapScheme n).Opens) [Nonempty U] :
    Function.Injective (regularValue n U) :=
  (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm.injective.comp
    ((overlapScheme n).germToFunctionField_injective U)

/-- Entire image, proved using the old actual frame's surjectivity.
This is not generator agreement or a bare dimension argument. -/
lemma full_image (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U]
    (z : (originalCubicScheme n).functionField) :
    (∃ s : Γ(overlapIdeal n i,U),
      ActualTwoDescentOriginalOverlapRationalFrameRebuild318.value n i U s=z) ↔
    ∃ a : Γ(overlapScheme n,U),regularValue n U a=z := by
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(affineValue n i).app U s,rfl⟩
  · rintro ⟨a,ha⟩
    letI := actual_affine_value_isIso n i
    have hb := (ConcreteCategory.isIso_iff_bijective ((affineValue n i).app U)).mp
      (inferInstance : IsIso ((affineValue n i).app U))
    obtain ⟨s,hs⟩ := hb.surjective a
    refine ⟨s,?_⟩
    change regularValue n U ((affineValue n i).app U s)=z
    rw [hs,ha]
end ActualTwoDescentOriginalOverlapValueImageRebuild318
