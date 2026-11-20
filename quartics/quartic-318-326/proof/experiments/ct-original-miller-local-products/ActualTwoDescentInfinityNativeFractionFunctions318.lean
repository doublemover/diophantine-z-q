module
public import ActualTwoDescentInfinityNativeDomain318
public section
noncomputable section
namespace ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeDomain318
variable {K : Type*} [Field K] [CharZero K]

/-- The actual fraction field of the original infinity local ring.
Its equivalence with the earlier affine FunctionField remains separate. -/
abbrev InfinityFractionField (n : K) := FractionRing (InfinityLocalRing n)
def infinityFractionMap (n : K) : InfinityLocalRing n →+* InfinityFractionField n := algebraMap _ _
def infinityAffineX (n : K) : InfinityFractionField n :=
  infinityFractionMap n (localU n)/infinityFractionMap n (localV n)
def infinityAffineY (n : K) : InfinityFractionField n := 1/infinityFractionMap n (localV n)

lemma actual_infinity_fraction_u_nonzero (n : K) : infinityFractionMap n (localU n) ≠ 0 := by
  intro h
  apply actual_local_u_nonzero n
  apply IsFractionRing.injective (InfinityLocalRing n) (InfinityFractionField n)
  simpa only [map_zero] using h

end ActualTwoDescentInfinityNativeFractionFunctions318
