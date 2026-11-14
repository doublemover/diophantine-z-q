module
public import ActualTwoDescentInfinityNormalizedOrders318
public section
noncomputable section
namespace ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeDomain318
open ActualTwoDescentInfinityFieldPoleComparison318 ActualTwoDescentInfinityNormalizedOrders318
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

/-- The formerly supplied field-map interface is now instantiated with
the produced native fraction map and its proved nonzero parameter. -/
theorem actual_native_infinity_root_normalization (n a : K) :
    ∃ e d : (InfinityLocalRing n)ˣ,
      localV n=(e : InfinityLocalRing n)*localU n^3 ∧
      localU n-localCoefficient n a*localV n=localU n*(d : InfinityLocalRing n) ∧
      infinityFractionMap n (localV n) ≠ 0 ∧
      (infinityAffineX n-infinityFractionMap n (localCoefficient n a))*
        infinityFractionMap n (localU n)^2=
        infinityFractionMap n (d : InfinityLocalRing n)/infinityFractionMap n (e : InfinityLocalRing n) ∧
      infinityFractionMap n (d : InfinityLocalRing n)/infinityFractionMap n (e : InfinityLocalRing n) ≠ 0 ∧
      infinityAffineY n*infinityFractionMap n (localU n)^3=
        1/infinityFractionMap n (e : InfinityLocalRing n) :=
  actual_root_function_unit_normalization n a (infinityFractionMap n)
    (actual_infinity_fraction_u_nonzero n)

end ActualTwoDescentInfinityNativeFractionFunctions318
