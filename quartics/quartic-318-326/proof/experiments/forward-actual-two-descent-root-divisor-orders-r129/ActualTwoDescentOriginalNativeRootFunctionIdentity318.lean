module
public import ActualTwoDescentOriginalNativeFieldCoordinates318
public section
noncomputable section
namespace ActualTwoDescentOriginalNativeRootFunctionIdentity318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityNativeFractionFunctions318 ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318 ActualTwoDescentOriginalNativeFieldCoordinates318
variable {K : Type*} [Field K] [CharZero K]

/-- Literal image of the EARLIER named original functionX, not merely
a newly introduced coordinate in an abstractly isomorphic field. -/
lemma actual_named_function_x (n : K) :
    originalNativeFunctionFieldEquiv n (functionX n)=infinityAffineX n :=
  actual_original_field_x n
lemma actual_named_coefficient (n a : K) :
    originalNativeFunctionFieldEquiv n (functionCoefficientMap n a)=
      infinityFractionMap n (localCoefficient n a) :=
  actual_original_field_coefficient n a

/-- All original affine root functions have the exact expected image
in the fraction field of the original infinity DVR, with coefficients fixed. -/
theorem actual_original_root_function (n a : K) :
    originalNativeFunctionFieldEquiv n (rootFunction n a)=
      infinityAffineX n-infinityFractionMap n (localCoefficient n a) := by
  rw [actual_root_function_identity,map_sub,actual_named_function_x,actual_named_coefficient]

/-- The original root function itself now consumes the produced local
unit normalization. This closes the former arbitrary-field-map interface,
but does not by itself glue a projective Cartier divisor. -/
theorem actual_original_root_pole_normalization (n a : K) :
    ∃ e d : (InfinityLocalRing n)ˣ,
      localV n=(e : InfinityLocalRing n)*localU n^3 ∧
      localU n-localCoefficient n a*localV n=localU n*(d : InfinityLocalRing n) ∧
      originalNativeFunctionFieldEquiv n (rootFunction n a)*
        infinityFractionMap n (localU n)^2=
        infinityFractionMap n (d : InfinityLocalRing n)/infinityFractionMap n (e : InfinityLocalRing n) ∧
      infinityFractionMap n (d : InfinityLocalRing n)/infinityFractionMap n (e : InfinityLocalRing n) ≠ 0 := by
  obtain ⟨e,d,hv,hd,hvn,hr,hrn,hy⟩ := actual_native_infinity_root_normalization n a
  refine ⟨e,d,hv,hd,?_,hrn⟩
  rw [actual_original_root_function]
  exact hr
end ActualTwoDescentOriginalNativeRootFunctionIdentity318
