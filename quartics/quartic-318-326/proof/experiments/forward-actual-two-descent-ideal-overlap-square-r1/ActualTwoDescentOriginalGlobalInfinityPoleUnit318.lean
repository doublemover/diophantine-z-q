module
public import ActualTwoDescentInfinityGlobalPrincipalIdeals318
public section
noncomputable section
namespace ActualTwoDescentOriginalGlobalInfinityPoleUnit318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityNativeDomain318 ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318 ActualTwoDescentOriginalNativeRootFunctionIdentity318
open ActualTwoDescentInfinityGlobalFactorUnit318 ActualTwoDescentInfinityGlobalRootUnits318
variable {K : Type*} [Field K] [CharZero K]

def chartFieldMap (n : K) : InfinityChart n →+* InfinityFractionField n :=
  (infinityFractionMap n).comp (algebraMap (InfinityChart n) (InfinityLocalRing n))
def rootPoleUnit (n : K) (i : Fin 3) : (InfinityChart n)ˣ :=
  globalRootUnit n i*(globalCubeUnit n)⁻¹

/-- The old ORIGINAL root function times u² is the image of an explicit
unit of the ENTIRE infinity chart. This is whole-chart Cartier data,
strictly stronger than a unit at the single origin local ring. -/
theorem actual_original_global_pole_unit (n : K) (i : Fin 3) :
    originalNativeFunctionFieldEquiv n (rootFunction n (root n i))*
      chartFieldMap n (chartU n)^2=chartFieldMap n (rootPoleUnit n i : InfinityChart n) := by
  let φ := chartFieldMap n
  have hu : φ (chartU n) ≠ 0 := actual_infinity_fraction_u_nonzero n
  have he0 : φ (globalCubeUnit n : InfinityChart n) ≠ 0 := ((globalCubeUnit n).isUnit.map φ).ne_zero
  have hv : φ (chartV n)=φ (globalCubeUnit n : InfinityChart n)*φ (chartU n)^3 := by
    rw [actual_global_v_unit_cube,map_mul,map_pow]
  have hv0 : φ (chartV n) ≠ 0 := by rw [hv]; exact mul_ne_zero he0 (pow_ne_zero _ hu)
  have hd : φ (chartU n)-φ (chartCoefficient n (root n i))*φ (chartV n)=
      φ (chartU n)*φ (globalRootUnit n i : InfinityChart n) := by
    rw [actual_global_root_unit_value]
    simpa only [map_sub,map_mul] using congrArg φ (actual_global_root_numerator n i)
  have hunit : φ (rootPoleUnit n i : InfinityChart n)=
      φ (globalRootUnit n i : InfinityChart n)/φ (globalCubeUnit n : InfinityChart n) := by
    have hi := congrArg φ (Units.mul_inv (globalCubeUnit n))
    simp only [map_mul,map_one] at hi
    have hh := ActualTwoDescentAffineChartCoordinates318.actual_inverse_unique
      (φ (globalCubeUnit n : InfinityChart n))
      (φ ((globalCubeUnit n)⁻¹ : (InfinityChart n)ˣ))
      ((φ (globalCubeUnit n : InfinityChart n))⁻¹) hi (mul_inv_cancel₀ he0)
    change φ ((globalRootUnit n i : InfinityChart n)*
      (((globalCubeUnit n)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n))=_
    rw [map_mul,hh,div_eq_mul_inv]
  rw [actual_original_root_function]
  change (φ (chartU n)/φ (chartV n)-φ (chartCoefficient n (root n i)))*φ (chartU n)^2=_
  rw [hunit]
  calc
    _=((φ (chartU n)-φ (chartCoefficient n (root n i))*φ (chartV n))/φ (chartV n))*
      φ (chartU n)^2 := by field_simp [hv0] <;> ring
    _=_ := by rw [hd,hv]; field_simp [he0,hu] <;> ring

lemma actual_original_global_pole_unit_nonzero (n : K) (i : Fin 3) :
    chartFieldMap n (rootPoleUnit n i : InfinityChart n) ≠ 0 :=
  ((rootPoleUnit n i).isUnit.map (chartFieldMap n)).ne_zero
end ActualTwoDescentOriginalGlobalInfinityPoleUnit318
