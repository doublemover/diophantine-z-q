module
public import ActualOriginalAmbientNormalIntegral318
public import Mathlib.Analysis.Fourier.FourierTransform
public section
noncomputable section
namespace ActualOriginalAmbientFourierIdentity318
open QuadricCRTAssembly318 ActualOriginalNormalProfile318 ActualOriginalGaussianMassRecovery318
open ActualOriginalAmbientNormalIntegral318 MeasureTheory
open scoped FourierTransform
set_option maxHeartbeats 16000000

/-- The exact standard negative Fourier phase, with its2pi normalization. -/
@[expose] def originalPhase (t s : ℝ) : ℂ :=
  Complex.exp (↑(-2*Real.pi*s*t)*Complex.I)
@[expose] def originalOscillation (κ : ℝ) (W : Coordinates ℝ→ℝ) (t : ℝ) : ℂ :=
  ∫x : Coordinates ℝ,W x • originalPhase t (equation κ x)
lemma originalPhase_continuous (t : ℝ) : Continuous (originalPhase t) := by
  unfold originalPhase
  fun_prop
lemma real_smul_original_phase (r : ℝ) (z : ℂ) : r • z=z • (r:ℂ) := by
  rw [RCLike.real_smul_eq_coe_mul,smul_eq_mul]
  exact mul_comm _ _

/-- The Fourier transform of the actual normal marginal is EXACTLY the
oscillatory integral on the ORIGINAL five-coordinate ambient source, with
ordinary original volume and the stated negative2pi phase. -/
theorem actual_original_ambient_fourier_identity (κ η : ℝ) (hη : 0<η)
    (W : Coordinates ℝ→ℝ) (hW : Continuous W) (hWc : HasCompactSupport W)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) (t : ℝ) :
    originalOscillation κ W t=𝓕 (complexProfile κ W) t := by
  rw [originalOscillation,
    actual_original_ambient_normal_integral κ η hη W hW hWc hb
      (originalPhase t) (originalPhase_continuous t),
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with s
  exact real_smul_original_phase (normalProfile κ W s) (originalPhase t s)

end ActualOriginalAmbientFourierIdentity318
