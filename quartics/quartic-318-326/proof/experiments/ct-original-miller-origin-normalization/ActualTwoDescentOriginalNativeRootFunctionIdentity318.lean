module
public import ActualTwoDescentOriginalNativeFieldCoordinates318
import all ActualTwoDescentAffineChartCoordinates318
import all ActualTwoDescentOriginalFunctionFieldTheta318
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

end ActualTwoDescentOriginalNativeRootFunctionIdentity318
