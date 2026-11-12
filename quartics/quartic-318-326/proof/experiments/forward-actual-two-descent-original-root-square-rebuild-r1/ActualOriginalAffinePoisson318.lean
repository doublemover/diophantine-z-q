module
public import ActualOriginalAffineFourier318
public section
noncomputable section
namespace ActualOriginalAffinePoisson318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalCompactFourier318 ActualOriginalPoissonSummation318
open ActualOriginalAffineInput318 ActualOriginalAffineFourier318
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- Poisson on every shifted and positively dilated copy of the same
integer lattice, with explicit original Fourier normalization. -/
theorem actual_original_affine_poisson (f : Coordinates ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c : Coordinates ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∑' z : Coordinates ℤ, f (c+R • integerEmbed z)) =
      ∑' m : Coordinates ℤ,
        (Real.fourierChar (frequency (R⁻¹ • integerEmbed m) c) : ℂ) *
          ((R^5)⁻¹ • compactFourier f (R⁻¹ • integerEmbed m)) := by
  rw [show (∑' z : Coordinates ℤ, f (c+R • integerEmbed z)) =
      ∑' z : Coordinates ℤ, affineInput f c R (integerEmbed z) from rfl]
  rw [actual_original_poisson _ (actual_affine_input_smooth f hf c R)
    (actual_affine_input_compact f hc c hR.ne')]
  exact tsum_congr (fun m => actual_original_affine_fourier f c (integerEmbed m) hR)

/-- Absolute convergence is carried through the SAME affine Fourier
identity, rather than assumed after formally rewriting an infinite sum. -/
theorem actual_original_affine_dual_summable (f : Coordinates ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c : Coordinates ℝ)
    {R : ℝ} (hR : 0 < R) :
    Summable (fun m : Coordinates ℤ =>
      ‖(Real.fourierChar (frequency (R⁻¹ • integerEmbed m) c) : ℂ) *
        ((R^5)⁻¹ • compactFourier f (R⁻¹ • integerEmbed m))‖) := by
  have h := (actual_compact_fourier_lattice_summable _
    (actual_affine_input_smooth f hf c R) (actual_affine_input_compact f hc c hR.ne')).1
  simpa only [actual_original_affine_fourier f c _ hR] using h

end ActualOriginalAffinePoisson318
