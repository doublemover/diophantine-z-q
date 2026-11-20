module
public import ActualMillerNormalizedFunction318
public import ActualMillerInfinityChartMap318
public import ActualTwoDescentOriginalNativeRootFunctionIdentity318
public import ActualTwoDescentInfinityNativeDVR318
public import ActualMillerRegularEvaluation318
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
import all ActualMillerNormalizedFunction318
import all ActualMillerInfinityChartMap318
import all ActualTwoDescentInfinityNativeFractionFunctions318
import all ActualTwoDescentInfinityLocalParameter318
public section
noncomputable section

namespace ActualMillerInfinityNormalization318

open ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityNativeDomain318 ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
open ActualTwoDescentOriginalNativeFieldCoordinates318
open ActualTwoDescentOriginalNativeRootFunctionIdentity318
open ActualTwoDescentOriginalGlobalInfinityPoleUnit318
open ActualTwoDescentInfinityMaximalGenerator318 ActualTwoDescentInfinityNativeDVR318

variable {K : Type*} [Field K] [CharZero K]

def clearedNumerator (n x y a : K) : InfinityChart n :=
  (1 - chartCoefficient n a * (chartU n - chartCoefficient n x * chartV n) -
    chartCoefficient n y * chartV n) * chartFactor n

def clearedDenominator (n z : K) : InfinityChart n :=
  chartFactor n - chartCoefficient n z * chartU n ^ 2

theorem cleared_numerator_at_origin (n x y a : K) :
    originEvaluation n (clearedNumerator n x y a) = 1 := by
  simp [clearedNumerator]

theorem cleared_denominator_at_origin (n z : K) :
    originEvaluation n (clearedDenominator n z) = 1 := by
  simp [clearedDenominator]

/-- An origin-one chart term is an actual unit in the native local ring. -/
theorem origin_one_local_unit (n : K) (q : InfinityChart n)
    (h : originEvaluation n q = 1) :
    IsUnit (algebraMap (InfinityChart n) (InfinityLocalRing n) q) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (InfinityLocalRing n) (originIdeal n) q).mpr
  change originEvaluation n q ≠ 0
  rw [h]
  exact one_ne_zero

private theorem chart_field_injective (n : K) : Function.Injective (chartFieldMap n) :=
  (IsFractionRing.injective (InfinityLocalRing n) (InfinityFractionField n)).comp
    (actual_local_map_injective n)

private theorem chart_field_ne_zero (n : K) (q : InfinityChart n) (hq : q ≠ 0) :
    chartFieldMap n q ≠ 0 := by
  intro h
  apply hq
  apply chart_field_injective n
  simpa only [map_zero] using h

private theorem chart_field_denominator_ne_zero (n z : K) :
    chartFieldMap n (clearedDenominator n z) ≠ 0 := by
  apply chart_field_ne_zero
  intro h
  have hz := cleared_denominator_at_origin n z
  rw [h, map_zero] at hz
  exact zero_ne_one hz

private theorem scaled_field_identity {M : Type*} [Field M]
    (U V F X₀ Y₀ A Z : M) (h : V * F = U^3)
    (hU : U ≠ 0) (hV : V ≠ 0) (hDen : F - Z * U^2 ≠ 0) :
    (-U) * ((A * (U / V - X₀) + Y₀ - 1 / V) / (U / V - Z)) =
      (1 - A * (U - X₀ * V) - Y₀ * V) * F / (F - Z * U^2) := by
  let N := 1 - A * (U - X₀ * V) - Y₀ * V
  have hB : (U - Z * V) * F = U * (F - Z * U^2) := by
    calc
      _ = U * F - Z * (V * F) := by ring
      _ = _ := by rw [h]; ring
  have hB₀ : U - Z * V ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hB
    exact (mul_ne_zero hU hDen) hB.symm
  have hSub : U / V - Z = (U - Z * V) / V := by
    field_simp [hV] <;> ring
  have hLine : A * (U / V - X₀) + Y₀ - 1 / V = -N / V := by
    dsimp [N]
    field_simp [hV] <;> ring
  rw [hSub, hLine]
  change (-U) * ((-N / V) / ((U - Z * V) / V)) = N * F / (F - Z * U^2)
  calc
    _ = (U * N) / (U - Z * V) := by field_simp [hV, hB₀] <;> ring
    _ = _ := (div_eq_div_iff hB₀ hDen).mpr (by linear_combination -N*hB)

/-- The t=-X/Y-normalized form on the ACTUAL infinity chart. The two
displayed chart terms take value 1 at O, so the normalized fraction
is a unit with residue 1, not just some unspecified nonzero scalar. -/
theorem actual_nonvertical_miller_origin (n x y a z : K) :
    (-chartFieldMap n (chartU n)) *
        originalNativeFunctionFieldEquiv n (nonverticalFunction n x y a z) =
      chartFieldMap n (clearedNumerator n x y a) / chartFieldMap n (clearedDenominator n z) ∧
      originEvaluation n (clearedNumerator n x y a) = 1 ∧
      originEvaluation n (clearedDenominator n z) = 1 := by
  refine ⟨?_, cleared_numerator_at_origin n x y a, cleared_denominator_at_origin n z⟩
  let φ := chartFieldMap n
  have hrel : φ (chartV n) * φ (chartFactor n) = (φ (chartU n))^3 := by
    simpa only [map_mul, map_pow] using congrArg φ (actual_chart_cubic_relation n)
  have hU : φ (chartU n) ≠ 0 := actual_infinity_fraction_u_nonzero n
  have hV := chart_field_ne_zero n (chartV n) (actual_chart_v_nonzero n)
  have hDen : φ (chartFactor n) - φ (chartCoefficient n z) * (φ (chartU n))^2 ≠ 0 := by
    simpa only [φ, clearedDenominator, map_sub, map_mul, map_pow] using
      chart_field_denominator_ne_zero n z
  simp only [nonverticalFunction, map_div₀, map_sub, map_add, map_mul,
    actual_named_function_x, actual_named_coefficient, actual_original_field_y,
    clearedNumerator, clearedDenominator, map_pow, map_one]
  exact scaled_field_identity (φ (chartU n)) (φ (chartV n)) (φ (chartFactor n))
    (φ (chartCoefficient n x)) (φ (chartCoefficient n y)) (φ (chartCoefficient n a))
    (φ (chartCoefficient n z)) hrel hU hV hDen

/-- Vertical factors have pole order two, with leading coefficient
one for the same t (whose square is the same as u²). -/
theorem actual_vertical_miller_origin (n x : K) :
    (-chartFieldMap n (chartU n)) ^ 2 *
        originalNativeFunctionFieldEquiv n (rootFunction n x) =
      chartFieldMap n (clearedDenominator n x) ∧
      originEvaluation n (clearedDenominator n x) = 1 := by
  refine ⟨?_, cleared_denominator_at_origin n x⟩
  let φ := chartFieldMap n
  have hrel : φ (chartV n) * φ (chartFactor n) = (φ (chartU n))^3 := by
    simpa only [map_mul, map_pow] using congrArg φ (actual_chart_cubic_relation n)
  have hV := chart_field_ne_zero n (chartV n) (actual_chart_v_nonzero n)
  have hcube : (φ (chartU n))^3 / φ (chartV n) = φ (chartFactor n) :=
    (div_eq_iff hV).mpr (by rw [← hrel, mul_comm])
  rw [actual_original_root_function]
  change (-φ (chartU n))^2 * (φ (chartU n) / φ (chartV n) - φ (chartCoefficient n x)) =
    φ (clearedDenominator n x)
  rw [clearedDenominator, map_sub, map_mul, map_pow]
  calc
    _ = ((φ (chartU n))^3 / φ (chartV n)) -
        φ (chartCoefficient n x) * (φ (chartU n))^2 := by field_simp [hV] <;> ring
    _ = _ := by rw [hcube]

/-- Actual residue evaluation on the native local ring at O. This is
the original chart evaluation extended through its prime complement. -/
def originResidue (n : K) : InfinityLocalRing n →+* K :=
  IsLocalization.lift (M := (originIdeal n).primeCompl) (g := originEvaluation n)
    (fun q => isUnit_iff_ne_zero.mpr (show originEvaluation n (q : InfinityChart n) ≠ 0 from q.property))

@[simp] theorem origin_residue_on_chart (n : K) (q : InfinityChart n) :
    originResidue n (algebraMap (InfinityChart n) (InfinityLocalRing n) q) = originEvaluation n q :=
  IsLocalization.lift_eq _ _

/-- The sign is the one in the literal affine rational parameter
minus x/y, not a new choice up to a unit. -/
theorem actual_signed_parameter_field (n : K) :
    originalNativeFunctionFieldEquiv n
      (-(functionX n / algebraMap (AffineChart n) (OriginalFunctionField n) (affineY n))) =
      infinityFractionMap n (-localU n) := by
  rw [map_neg, map_div₀, actual_named_function_x, actual_original_field_y]
  change -(chartFieldMap n (chartU n) / chartFieldMap n (chartV n) /
      (1 / chartFieldMap n (chartV n))) = -chartFieldMap n (chartU n)
  have hv := chart_field_ne_zero n (chartV n) (actual_chart_v_nonzero n)
  field_simp [hv] <;> ring

theorem actual_signed_parameter_uniformizer (n : K) : Irreducible (-localU n) := by
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (-localU n)
    (neg_ne_zero.mpr (actual_local_u_nonzero n))
  rw [Ideal.span_singleton_neg]
  exact actual_infinity_maximal_principal n

/-- The identical native fraction already used at affine points has
pole order one at O with respect to t=-x/y, with the actual local unit
having exactly residue 1. -/
theorem actual_nonvertical_miller_origin_unit (n x y a z : K) :
    ∃ e : (InfinityLocalRing n)ˣ,
      infinityFractionMap n (-localU n) * originalNativeFunctionFieldEquiv n
        (nonverticalFunction n x y a z) = infinityFractionMap n (e : InfinityLocalRing n) ∧
      originResidue n (e : InfinityLocalRing n) = 1 := by
  let i : InfinityChart n →+* InfinityLocalRing n := algebraMap _ _
  obtain ⟨h, hN, hD⟩ := actual_nonvertical_miller_origin n x y a z
  obtain ⟨N, hNu⟩ := origin_one_local_unit n (clearedNumerator n x y a) hN
  obtain ⟨D, hDu⟩ := origin_one_local_unit n (clearedDenominator n z) hD
  have hN' : (N : InfinityLocalRing n) = i (clearedNumerator n x y a) := hNu
  have hD' : (D : InfinityLocalRing n) = i (clearedDenominator n z) := hDu
  refine ⟨N * D⁻¹, ?_, ?_⟩
  · have he : infinityFractionMap n (↑(N * D⁻¹) : InfinityLocalRing n) =
        chartFieldMap n (clearedNumerator n x y a) / chartFieldMap n (clearedDenominator n z) := by
      rw [Units.val_mul, map_mul, map_units_inv, hN', hD', div_eq_mul_inv] <;> rfl
    rw [he]
    simpa only [map_neg] using h
  · rw [Units.val_mul, map_mul, map_units_inv, hN', hD']
    change originResidue n (algebraMap _ _ (clearedNumerator n x y a)) *
      (originResidue n (algebraMap _ _ (clearedDenominator n z)))⁻¹ = 1
    simp only [origin_residue_on_chart, hN, hD, inv_one, one_mul]

/-- The actual vertical branch has pole order two for the same t,
again with local leading residue exactly 1. -/
theorem actual_vertical_miller_origin_unit (n x : K) :
    ∃ e : (InfinityLocalRing n)ˣ,
      (infinityFractionMap n (-localU n))^2 * originalNativeFunctionFieldEquiv n
        (rootFunction n x) = infinityFractionMap n (e : InfinityLocalRing n) ∧
      originResidue n (e : InfinityLocalRing n) = 1 := by
  obtain ⟨h, hD⟩ := actual_vertical_miller_origin n x
  obtain ⟨D, hDu⟩ := origin_one_local_unit n (clearedDenominator n x) hD
  refine ⟨D, ?_, ?_⟩
  · rw [hDu]
    simpa only [map_neg] using h
  · rw [hDu, origin_residue_on_chart, hD]

/-- The identical section chosen on the affine principal open gives
the same native unit certificate at infinity. No collision-free point
evaluation hypotheses are carried into this meromorphic statement. -/
theorem actual_regular_section_origin_unit (n x y a z : K) :
    ∃ e : (InfinityLocalRing n)ˣ,
      infinityFractionMap n (-localU n) * originalNativeFunctionFieldEquiv n
        (ActualMillerRegularEvaluation318.openIntoFunction n z
          (ActualMillerRegularEvaluation318.regularLineSection n x y a z)) =
        infinityFractionMap n (e : InfinityLocalRing n) ∧
      originResidue n (e : InfinityLocalRing n) = 1 := by
  rw [ActualMillerRegularEvaluation318.regular_section_is_same_function]
  exact actual_nonvertical_miller_origin_unit n x y a z

end ActualMillerInfinityNormalization318
