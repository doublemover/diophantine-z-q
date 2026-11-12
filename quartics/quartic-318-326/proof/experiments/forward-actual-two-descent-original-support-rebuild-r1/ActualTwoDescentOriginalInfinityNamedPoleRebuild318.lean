module
public import ActualTwoDescentOriginalInfinityLocalFieldRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityNamedPoleRebuild318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentOriginalInfinityLocalFieldRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- The actual local uniformizer and actual local units normalize the
SAME original root function. No abstract principal-divisor map is assumed. -/
theorem normalization (n a : K) :
    ∃ e d : (InfinityLocalRing n)ˣ,
      localV n=(e : InfinityLocalRing n)*localU n^3 ∧
      localU n-localCoefficient n a*localV n=localU n*(d : InfinityLocalRing n) ∧
      infinityFractionMap n (localV n) ≠ 0 ∧
      comparison n (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a)*
        infinityFractionMap n (localU n)^2=
        infinityFractionMap n (d : InfinityLocalRing n)/infinityFractionMap n (e : InfinityLocalRing n) ∧
      infinityFractionMap n (d : InfinityLocalRing n)/infinityFractionMap n (e : InfinityLocalRing n) ≠ 0 := by
  obtain ⟨e,d,he,hd,hv,hr,hunit,_⟩ := actual_native_infinity_root_normalization n a
  exact ⟨e,d,he,hd,hv,by rw [named_root]; exact hr,hunit⟩
end ActualTwoDescentOriginalInfinityNamedPoleRebuild318
