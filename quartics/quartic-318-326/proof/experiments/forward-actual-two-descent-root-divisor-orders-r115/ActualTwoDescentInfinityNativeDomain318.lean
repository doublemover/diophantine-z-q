module
public import ActualTwoDescentInfinitySwapEquivalence318
public section
noncomputable section
namespace ActualTwoDescentInfinityNativeDomain318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinitySwappedCubic318 ActualTwoDescentInfinityEisenstein318
open ActualTwoDescentInfinitySwapEquivalence318
variable {K : Type*} [Field K] [CharZero K]

/-- Integrality of the ORIGINAL chart is produced by the explicit swap
and Eisenstein argument, not postulated for a surrogate normalization. -/
instance infinityChartDomain (n : K) : IsDomain (InfinityChart n) :=
  (infinitySwapEquiv n).symm.injective.isDomain

instance infinityLocalDomain (n : K) : IsDomain (InfinityLocalRing n) :=
  IsLocalization.isDomain_of_local_atPrime (originIdealPrime n)

lemma actual_chart_u_nonzero (n : K) : chartU n ≠ 0 := by
  intro h
  have hh := congrArg (originalToSwap n) h
  exact actual_swapped_u_nonzero n (by simpa only [actual_original_to_swap_u,map_zero] using hh)

lemma actual_chart_v_nonzero (n : K) : chartV n ≠ 0 := by
  intro h
  have hh := congrArg (originalToSwap n) h
  exact actual_swapped_v_nonzero n (by simpa only [actual_original_to_swap_v,map_zero] using hh)

lemma actual_local_map_injective (n : K) :
    Function.Injective (algebraMap (InfinityChart n) (InfinityLocalRing n)) :=
  IsLocalization.injective (InfinityLocalRing n) (originIdeal n).primeCompl_le_nonZeroDivisors

lemma actual_local_u_nonzero (n : K) : localU n ≠ 0 := by
  intro h
  apply actual_chart_u_nonzero n
  apply actual_local_map_injective n
  simpa only [map_zero] using h

lemma actual_local_v_nonzero (n : K) : localV n ≠ 0 := by
  intro h
  apply actual_chart_v_nonzero n
  apply actual_local_map_injective n
  simpa only [map_zero] using h

end ActualTwoDescentInfinityNativeDomain318
