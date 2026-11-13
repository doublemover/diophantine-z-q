module
public import ActualTwoDescentOriginalInfinityStalkPoleRebuild318
public import ActualDvrMeromorphicOrder318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootMeromorphicOrderRebuild318
open AlgebraicGeometry IsDiscreteValuationRing
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Native normalized valuation on the actual original generic field,
not a separately selected rational-function field. -/
def value (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    AddValuation (originalCubicScheme n).functionField (WithTop ℤ) :=
  ActualDvrMeromorphicOrder318.value (RootStalk n i) (originalCubicScheme n).functionField

theorem named_root (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    value n i (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
      (ActualTwoDescentOriginalRootIdeals318.root n i)) = (2 : WithTop ℤ) := by
  rw [←ActualTwoDescentOriginalRootGenericSquareRebuild318.root_square]
  change ActualDvrMeromorphicOrder318.value (RootStalk n i) _ _ = _
  rw [ActualDvrMeromorphicOrder318.value_integral _ _ _
    (ActualTwoDescentOriginalRootGenericSquareRebuild318.root_nonzero_in_stalk n i),
    ActualTwoDescentOriginalStalkOrdersRebuild318.root_f_order]
  norm_num

theorem integral_order (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    ActualDvrMeromorphicOrder318.order (RootStalk n i) (originalCubicScheme n).functionField
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i)) = 2 :=
  ActualDvrMeromorphicOrder318.order_eq _ _ _ 2 (named_root n i)
end ActualTwoDescentOriginalRootMeromorphicOrderRebuild318
