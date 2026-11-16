module
public import ActualOriginalZeroModeCoefficient318
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public section
noncomputable section
namespace ActualOriginalPositiveSingularIntegral318
open QuadricCRTAssembly318 ActualOriginalCoordinateFrequency318 ActualOriginalTwistedWeight318
open ActualOriginalAmbientFourierIdentity318 MeasureTheory Filter
set_option maxHeartbeats 16000000

/-- Exact reflection between the positive circle-method phase and the
negative Fourier phase of the previously proved undamped singular integral. -/
lemma actual_positive_zero_frequency (κ β : ℝ) (W : Coordinates ℝ → ℝ) :
    originalCoordinateFourier κ β W 0 = originalOscillation κ W (-β) := by
  rw [actual_coordinate_fourier_integral]
  unfold originalOscillation
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : 2*Real.pi*β*equation κ x = -2*Real.pi*equation κ x*(-β) := by ring
  simp only [dot,Prod.fst_zero,Prod.snd_zero,zero_mul,zero_add,neg_zero,
    AddChar.map_zero_eq_one,one_smul,twistedWeight,originalPhase,RCLike.real_smul_eq_coe_mul]
  rw [hp]

lemma actual_positive_zero_integrable (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hi : Integrable (originalOscillation κ W)) :
    Integrable (fun β : ℝ => originalCoordinateFourier κ β W 0) := by
  simpa only [actual_positive_zero_frequency] using hi.comp_neg

lemma actual_positive_zero_integral (κ : ℝ) (W : Coordinates ℝ → ℝ) :
    (∫ β : ℝ, originalCoordinateFourier κ β W 0) = ∫ t : ℝ, originalOscillation κ W t := by
  simp_rw [actual_positive_zero_frequency]
  exact integral_neg_eq_self _ volume

/-- Truncation converges only after integrability of the exact positive
zero mode has been transferred from the proved undamped original integral. -/
theorem actual_positive_zero_cutoff (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hi : Integrable (originalOscillation κ W)) (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => ∫ β : ℝ in -T n..T n, originalCoordinateFourier κ β W 0)
      atTop (𝓝 (∫ t : ℝ, originalOscillation κ W t)) := by
  have h := intervalIntegral_tendsto_integral
    (actual_positive_zero_integrable κ W hi) (tendsto_neg_atTop_atBot.comp hT) hT
  simpa only [actual_positive_zero_integral] using h

end ActualOriginalPositiveSingularIntegral318
