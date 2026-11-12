module
public import ActualTwoDescentOpenAffineCoefficientSquareRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootGenericSquareRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentOriginalGenericFunctionsRebuild318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentOriginalRootEvaluation318
variable {K : Type*} [Field K] [CharZero K]

/-- The literal earlier root function in the actual native generic stalk
is the image of its exact original marked-stalk coordinate. -/
theorem root_square (n : K) (i : Fin 3) :
    algebraMap (RootStalk n i) (originalCubicScheme n).functionField (rootF n i) =
      ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i) := by
  apply (affineComparison n).injective
  rw [root_comparison, rootF_is_actual_coordinate]
  rw [ActualTwoDescentOpenAffineCoefficientSquareRebuild318.fraction_square]
  unfold ActualTwoDescentOriginalFunctionFieldTheta318.rootFunction
  rw [ActualTwoDescentRootCofactorData318.actual_root_numerator_class]

theorem root_nonzero_in_stalk (n : K) (i : Fin 3) : rootF n i ≠ 0 := by
  intro h
  have hh := root_square n i
  rw [h,map_zero] at hh
  exact root_nonzero n _ hh.symm
end ActualTwoDescentOriginalRootGenericSquareRebuild318
