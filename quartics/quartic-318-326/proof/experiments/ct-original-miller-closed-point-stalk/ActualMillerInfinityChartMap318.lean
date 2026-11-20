module
public import ActualTwoDescentInfinityNativeFractionFunctions318
public section
noncomputable section
namespace ActualTwoDescentOriginalGlobalInfinityPoleUnit318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeFractionFunctions318
variable {K : Type*} [Field K] [CharZero K]

def chartFieldMap (n : K) : InfinityChart n →+* InfinityFractionField n :=
  (infinityFractionMap n).comp (algebraMap (InfinityChart n) (InfinityLocalRing n))
end ActualTwoDescentOriginalGlobalInfinityPoleUnit318
