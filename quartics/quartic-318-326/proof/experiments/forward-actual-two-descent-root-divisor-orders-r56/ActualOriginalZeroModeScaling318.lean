module
public import ActualOriginalPositiveSingularIntegral318
public section
noncomputable section
namespace ActualOriginalZeroModeScaling318
open QuadricCRTAssembly318 ActualOriginalCoordinateFrequency318 ActualOriginalRationalPoisson318
open ActualOriginalZeroModeCoefficient318 ActualOriginalGlobalCoefficient318
open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The actual zero dual-frequency summand of rational-arc Poisson. -/
@[expose] def zeroModeArc (κ : ℤ) (q : ℕ) [NeZero q] (a : ℤ)
    (β B : ℝ) (W : Coordinates ℝ → ℝ) : ℂ :=
  completeArcCoefficient κ q a 0 *
    ((B/(q : ℝ))^5 • originalCoordinateFourier (κ : ℝ) (β*B^2) W 0)

/-- Original ambient scaling contributes B^5; the actual beta change of
variables contributes B^-2. The resulting zero mode is exactly B^3 times
the q^-5 complete coefficient and the same positive singular integral. -/
theorem actual_original_zero_mode_scaling (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (B T : ℝ) (hB : B ≠ 0) (W : Coordinates ℝ → ℝ) :
    (∫ β : ℝ in -T/B^2..T/B^2, zeroModeArc κ q a β B W) =
      (B : ℂ)^3 * ((completeArcCoefficient κ q a 0 / (q : ℂ)^5) *
        ∫ t : ℝ in -T..T, originalCoordinateFourier (κ : ℝ) t W 0) := by
  unfold zeroModeArc
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_smul,
    intervalIntegral.integral_comp_mul_right
      (fun t => originalCoordinateFourier (κ : ℝ) t W 0) (pow_ne_zero 2 hB)]
  have hleft : (-T/B^2)*B^2 = -T := by field_simp [hB]
  have hright : (T/B^2)*B^2 = T := by field_simp [hB]
  rw [hleft,hright]
  have hBC : (B : ℂ) ≠ 0 := by exact_mod_cast hB
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  simp only [RCLike.real_smul_eq_coe_mul,Complex.ofReal_pow,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_inv]
  field_simp [hBC,hqC]
  <;> ring


/-- Summing precisely the unit numerators gives the actual full singular
series coefficient, with no primitive-point correction factor. -/
theorem actual_original_unit_zero_mode_scaling (κ : ℤ) (q : ℕ) [NeZero q]
    (B T : ℝ) (hB : B ≠ 0) (W : Coordinates ℝ → ℝ) :
    (∑ a : {a : ZMod q // IsUnit a}, ∫ β : ℝ in -T/B^2..T/B^2,
      zeroModeArc κ q (a.val.val : ℤ) β B W) =
      (B : ℂ)^3 * (coefficient κ q *
        ∫ t : ℝ in -T..T, originalCoordinateFourier (κ : ℝ) t W 0) := by
  classical
  simp_rw [actual_original_zero_mode_scaling κ q _ B T hB W]
  rw [←Finset.mul_sum,←Finset.sum_mul,←Finset.sum_div,actual_zero_mode_coefficient]

end ActualOriginalZeroModeScaling318
