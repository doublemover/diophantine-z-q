module
public import ActualOriginalCompactCircleCount318
public import ActualOriginalFiniteMajorArcError318
public import ActualOriginalZeroModeLimit318
public section
noncomputable section
namespace ActualOriginalMajorArcIntegral318
open QuadricCRTAssembly318 ActualOriginalScaledCircle318 ActualOriginalCompactCircleCount318
open ActualOriginalZeroModeScaling318 ActualOriginalPositiveSingularIntegral318
open ActualOriginalCoordinateFrequency318 ActualOriginalAmbientFourierIdentity318
open ActualOriginalGlobalCoefficient318 ActualOriginalZeroModeLimit318
open ActualOriginalIntegratedArcError318 ActualOriginalFiniteMajorArcError318
open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Actual circle integrals on precisely the indexed arcs already used by
finiteMajorArcError. Unit numerators, modulus one, and all bad moduli remain. -/
@[expose] def majorArcIntegral (κ : ℤ) (N : ℕ) (B T : ℝ)
    (W : Coordinates ℝ → ℝ) : ℂ :=
  ∑ q : Fin N, ∑ a : {a : ZMod (q.val+1) // IsUnit a},
    ∫ β : ℝ in -T/B^2..T/B^2,
      scaledCircleSum κ ((a.val.val : ℝ)/((q.val+1 : ℕ) : ℝ)+β) B W

lemma actual_zero_arc_interval_integrable (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (B T : ℝ) (hB : B ≠ 0) (W : Coordinates ℝ → ℝ)
    (hi : Integrable (originalOscillation (κ : ℝ) W)) :
    IntervalIntegrable (fun β => zeroModeArc κ q a β B W) volume (-T/B^2) (T/B^2) := by
  have hf := (actual_positive_zero_integrable (κ : ℝ) W hi).comp_mul_right' (pow_ne_zero 2 hB)
  exact ((hf.intervalIntegrable.smul ((B/(q : ℝ))^5)).const_mul
    (ActualOriginalRationalPoisson318.completeArcCoefficient κ q a 0))

lemma actual_positive_denominator_sum (κ : ℤ) (N : ℕ) :
    (∑ q : Fin N, coefficient κ (q.val+1)) = ∑ q ∈ Finset.range (N+1), coefficient κ q := by
  induction N with
  | zero => simp [actual_coefficient_zero]
  | succ N ih =>
      rw [Fin.sum_univ_castSucc,Finset.sum_range_succ]
      simpa only [Fin.val_castSucc,Fin.val_last] using congrArg
        (fun z : ℂ => z+coefficient κ (N+1)) ih

/-- The finite rational-arc integral has the EXACT singular-series partial
sum as its zero mode and exactly the previously bounded full nonzero-mode
error. The sole +1 is the zero denominator assigned coefficient zero. -/
theorem actual_major_arc_decomposition (κ N : ℕ) (B T : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W)
    (hi : Integrable (originalOscillation (κ : ℝ) W)) :
    majorArcIntegral (κ : ℤ) N B T W =
      (B : ℂ)^3 * normalizedZeroMode (κ : ℤ) W (N+1) T + finiteMajorArcError κ N B T W := by
  classical
  have oneArc (q : Fin N) (a : {a : ZMod (q.val+1) // IsUnit a}) :
      (∫ β : ℝ in -T/B^2..T/B^2,
        scaledCircleSum (κ : ℤ) ((a.val.val : ℝ)/((q.val+1 : ℕ) : ℝ)+β) B W) =
      (∫ β : ℝ in -T/B^2..T/B^2,
        zeroModeArc (κ : ℤ) (q.val+1) (a.val.val : ℤ) β B W) +
      integratedArcError κ (q.val+1) (a.val.val : ℤ) B T W := by
    have hc := (actual_scaled_circle_continuous (κ : ℤ) B hB W hW).comp
      (continuous_const.add continuous_id)
    have hz := actual_zero_arc_interval_integrable (κ : ℤ) (q.val+1)
      (a.val.val : ℤ) B T hB W hi
    have he := intervalIntegral.integral_sub (hc.intervalIntegrable _ _) hz
    simp only [Int.cast_natCast] at he
    change integratedArcError κ (q.val+1) (a.val.val : ℤ) B T W = _ at he
    rw [he]
    ring
  unfold majorArcIntegral
  simp_rw [oneArc]
  simp_rw [Finset.sum_add_distrib]
  change (∑ q : Fin N, ∑ a : {a : ZMod (q.val+1) // IsUnit a},
    ∫ β : ℝ in -T/B^2..T/B^2, zeroModeArc (κ : ℤ) (q.val+1) (a.val.val : ℤ) β B W) +
    finiteMajorArcError κ N B T W = _
  simp_rw [actual_original_unit_zero_mode_scaling (κ : ℤ) _ B T hB W]
  rw [←Finset.mul_sum,←Finset.sum_mul,actual_positive_denominator_sum]
  rfl

end ActualOriginalMajorArcIntegral318
