module
public import ActualTwoDescentOriginalRootMeromorphicOrderRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

def value (n : K) : AddValuation (originalCubicScheme n).functionField (WithTop ℤ) :=
  ActualDvrMeromorphicOrder318.value (InfinityStalk n) (originalCubicScheme n).functionField

/-- The original pole has order MINUS two, for every root parameter a.
The actual unit quotient is retained before taking the valuation. -/
theorem named_root (n a : K) :
    value n (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a) = (-2 : WithTop ℤ) := by
  obtain ⟨e,d,hd⟩ := ActualTwoDescentOriginalInfinityStalkPoleRebuild318.fraction n a
  rw [hd,(value n).map_div,(value n).map_div,(value n).map_pow]
  change ActualDvrMeromorphicOrder318.value (InfinityStalk n) _ _ -
    ActualDvrMeromorphicOrder318.value (InfinityStalk n) _ _ -
    2 • ActualDvrMeromorphicOrder318.value (InfinityStalk n) _ _ = _
  rw [ActualDvrMeromorphicOrder318.value_unit _ _ _ d.isUnit,
    ActualDvrMeromorphicOrder318.value_unit _ _ _ e.isUnit,
    ActualDvrMeromorphicOrder318.value_uniformizer _ _ _
      (ActualTwoDescentOriginalStalkFactorsRebuild318.infinity_uniformizer n)]
  norm_num

theorem integral_order (n a : K) :
    ActualDvrMeromorphicOrder318.order (InfinityStalk n) (originalCubicScheme n).functionField
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a) = -2 :=
  ActualDvrMeromorphicOrder318.order_eq _ _ _ (-2) (named_root n a)
end ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318
