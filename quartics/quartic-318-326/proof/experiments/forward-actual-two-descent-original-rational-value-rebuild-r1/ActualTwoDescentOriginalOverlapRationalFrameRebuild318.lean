module
public import ActualTwoDescentOriginalGlobalRationalValueRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapRationalFrameRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalOverlapOldFrameComparison318
open ActualTwoDescentOriginalInverseInfinityTransition318
variable {K : Type*} [Field K] [CharZero K]

/-- Exact local frame value in the original field on EVERY nonempty
subopen of the literal common chart. -/
def value (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U]
    (s : Γ(overlapIdeal n i,U)) : (originalCubicScheme n).functionField :=
  (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
    ((overlapScheme n).germToFunctionField U ((affineValue n i).app U s))

lemma injective (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U] :
    Function.Injective (value n i U) := by
  letI := actual_affine_value_isIso n i
  have hb := (ConcreteCategory.isIso_iff_bijective ((affineValue n i).app U)).mp
    (inferInstance : IsIso ((affineValue n i).app U))
  exact (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm.injective.comp
    (((overlapScheme n).germToFunctionField_injective U).comp hb.injective)

/-- Full actual inverse-u transition, with the restricted section and
native field map retained. Not just equality at a chosen point. -/
lemma infinity_formula (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U]
    (s : Γ(overlapIdeal n i,U)) : value n i U s=
    (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
      ((overlapScheme n).germToFunctionField U ((infinityValue n i).app U s)) *
    (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
      ((overlapScheme n).germToFunctionField U
        ((overlapScheme n).presheaf.map (homOfLE (show U≤⊤ from le_top)).op
          (inverseUSection n))) := by
  unfold value
  rw [actual_overlap_values_apply,map_mul,map_mul]

lemma adjoint (n : K) (i : Fin 3) :
    (Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _
      (affineValue n i)=ActualTwoDescentOriginalGlobalRationalValueRebuild318.coefficientMap n i :=
  Equiv.apply_symm_apply _ _
end ActualTwoDescentOriginalOverlapRationalFrameRebuild318
