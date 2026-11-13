module
public import ActualTwoDescentDVRValueTransportRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalStalkOrdersRebuild318
open IsDiscreteValuationRing
open ActualTwoDescentOriginalMarkedStalksRebuild318
open ActualTwoDescentOriginalStalkFactorsRebuild318
open ActualTwoDescentOriginalRootNormalizedOrders318
open ActualTwoDescentInfinityNormalizedOrders318
open ActualTwoDescentInfinityLocalParameter318
variable {K : Type*} [Field K] [CharZero K]

theorem root_y_order (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    addVal (RootStalk n i) (rootY n i) = 1 :=
  addVal_uniformizer (root_uniformizer n i)
theorem root_f_order (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    addVal (RootStalk n i) (rootF n i) = 2 := by
  obtain ⟨e, he⟩ := root_factor n Fact.out i
  exact addVal_def _ e (root_uniformizer n i) 2 he
theorem infinity_u_order (n : K) :
    addVal (InfinityStalk n) (infinityU n) = 1 :=
  addVal_uniformizer (infinity_uniformizer n)
theorem infinity_v_order (n : K) :
    addVal (InfinityStalk n) (infinityV n) = 3 := by
  obtain ⟨e, he⟩ := infinity_factor n
  exact addVal_def _ e (infinity_uniformizer n) 3 he

/-- Every original root numerator at infinity has order one in the
actual original scheme stalk. The root value is an arbitrary a : K. -/
theorem infinity_root_order (n a : K) :
    addVal (InfinityStalk n)
      ((infinityEquiv n).symm (localU n - localCoefficient n a * localV n)) = 1 := by
  rw [ActualTwoDescentDVRValueTransportRebuild318.value]
  exact actual_infinity_order_root_numerator n a

/-- Exact normalization on every element, not merely the chosen coordinates. -/
theorem root_all_values (n : K) (i : Fin 3) [Fact (n ≠ 0)] (x : RootStalk n i) :
    addVal (ActualTwoDescentOriginalRootLocalParameter318.RootLocalRing n i)
      (rootEquiv n i x) = addVal (RootStalk n i) x :=
  ActualTwoDescentDVRValueTransportRebuild318.value _ _
theorem infinity_all_values (n : K) (x : InfinityStalk n) :
    addVal (InfinityLocalRing n) (infinityEquiv n x) = addVal (InfinityStalk n) x :=
  ActualTwoDescentDVRValueTransportRebuild318.value _ _
end ActualTwoDescentOriginalStalkOrdersRebuild318
