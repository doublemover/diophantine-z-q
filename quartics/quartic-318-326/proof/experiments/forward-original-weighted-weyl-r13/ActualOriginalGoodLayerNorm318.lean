module
public import ActualOriginalGlobalCoefficient318
public section
noncomputable section
namespace ActualOriginalGoodLayerNorm318
open ActualOriginalGlobalCoefficient318 ActualOriginalUnitLocalSeries318
open ActualOriginalLocalSeriesConvergence318 ActualGeometricLocalSeries318
open ActualFullLocalDensityRecurrence318 ActualLocalVolumeClosedForm318
open ActualLocalPrimitiveNormalization318 ActualOriginalLocalDensityLimit318
set_option maxHeartbeats 16000000

lemma actual_good_volume_step (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (h2 : p ≠ 2) (hκ : ¬(p : ℤ) ∣ κ) (n : ℕ) :
    volume κ p n ≤ volume κ p (n+1) := by
  have hr0 : (0 : ℚ) ≤ ratio p := by unfold ratio; positivity
  have hr1 : ratio p ≤ 1 := (ratio_lt_one p hp).le
  have hS : (1 : ℚ) ≤ localFactor p := (actual_factor_gt_one p hp).le
  have hpar : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hpar with he | ho
  · have h := actual_even_odd_formula κ p hp h2 hκ (n/2)
    exact le_of_eq (((congrArg (volume κ p) he).trans h.1).trans
      (((congrArg (fun j => volume κ p (j+1)) he).trans h.2).symm))
  · have h := actual_even_odd_formula κ p hp h2 hκ (n/2)
    have hnext := (actual_even_odd_formula κ p hp h2 hκ (n/2+1)).1
    have hi : n+1=2*(n/2+1) := by omega
    have hv := (congrArg (volume κ p) ho).trans h.2
    have hvnext := (congrArg (volume κ p) hi).trans hnext
    rw [hv,hvnext,pow_succ]
    have hpos := mul_nonneg (mul_nonneg (sub_nonneg.mpr hS)
      (pow_nonneg hr0 (n/2))) (sub_nonneg.mpr hr1)
    nlinarith

lemma actual_good_layers_nonnegative (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (h2 : p ≠ 2) (hκ : ¬(p : ℤ) ∣ κ) (n : ℕ) : 0 ≤ originalLayers κ p n := by
  cases n with
  | zero => simp only [originalLayers,layers,volume_zero,Rat.cast_one]; norm_num
  | succ n =>
    change 0 ≤ (volume κ p (n+1) : ℝ)-(volume κ p n : ℝ)
    exact sub_nonneg.mpr (by exact_mod_cast actual_good_volume_step κ p hp h2 hκ n)

/-- Good-prime absolute local factors equal the actual density, rather
than merely having an unspecified finite norm sum. Exceptional places will
be kept as finitely many separately convergent norm factors. -/
theorem actual_good_norm_series (κ : ℤ) (p : ℕ) [NeZero p] (hp : p.Prime)
    (h2 : p ≠ 2) (hκ : ¬(p : ℤ) ∣ κ) :
    HasSum (fun n => ‖coefficient κ (p^n)‖) (localFactor p : ℝ) := by
  have hs : HasSum (originalLayers κ p) (localFactor p : ℝ) :=
    actual_layers_hasSum _ _ _ (good_prime_error_summable κ p hp h2 hκ)
      (actual_original_local_density_limit κ p hp h2 hκ)
  have he (n : ℕ) : ‖coefficient κ (p^n)‖ = originalLayers κ p n := by
    rw [actual_coefficient_nonzero,actual_unit_frequency_real κ p hp,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (actual_good_layers_nonnegative κ p hp h2 hκ n)]
  simpa only [he] using hs

end ActualOriginalGoodLayerNorm318
