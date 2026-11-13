module
public import ActualTwoDescentPushforwardRationalValueRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalGlobalRationalValueRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentOriginalIdealOverlapValues318
variable {K : Type*} [Field K] [CharZero K]

/-- The old affine projection and literal ideal inclusion, restricted
through the COMPLETE actual overlap. No new gluing hypothesis is supplied. -/
def coefficientMap (n : K) (i : Fin 3) : originalRootIdealSheaf n i ⟶
    (Scheme.Modules.pushforward (overlapEmbedding n)).obj
      (ClutchedModule318.unit (overlapScheme n)) :=
  affineProjection n i ≫ affineIdealRestriction n i

lemma infinity_coefficientMap (n : K) (i : Fin 3) : coefficientMap n i=
    infinityProjection n i ≫ infinityInverseRestriction n :=
  actual_ideal_sheaf_compatibility n i

/-- Every nonempty ambient section now has a canonical value in the SAME
original generic field. Injectivity/global image is not asserted here. -/
def value (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U]
    (s : Γ(originalRootIdealSheaf n i,U)) : (originalCubicScheme n).functionField :=
  ActualTwoDescentPushforwardRationalValueRebuild318.value (overlapEmbedding n)
    (originalRootIdealSheaf n i) (coefficientMap n i) U s

lemma infinity_formula (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (s : Γ(originalRootIdealSheaf n i,U)) : value n i U s=
    ActualTwoDescentOpenRationalEvaluationRebuild318.evaluation (overlapEmbedding n) U
      ((infinityInverseRestriction n).app U ((infinityProjection n i).app U s)) := by
  unfold value ActualTwoDescentPushforwardRationalValueRebuild318.value
  rw [infinity_coefficientMap] <;> rfl

lemma restrict (n : K) (i : Fin 3) (U V : (originalCubicScheme n).Opens)
    [Nonempty U] [Nonempty V] (h : V ≤ U) (s : Γ(originalRootIdealSheaf n i,U)) :
    value n i V ((originalRootIdealSheaf n i).presheaf.map (homOfLE h).op s)=value n i U s :=
  ActualTwoDescentPushforwardRationalValueRebuild318.restrict _ _ _ U V h s

lemma scalar (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (a : Γ(originalCubicScheme n,U)) (s : Γ(originalRootIdealSheaf n i,U)) :
    value n i U (a • s)=(originalCubicScheme n).germToFunctionField U a*value n i U s :=
  ActualTwoDescentPushforwardRationalValueRebuild318.scalar _ _ _ U a s
end ActualTwoDescentOriginalGlobalRationalValueRebuild318
