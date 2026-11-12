module
public import ActualOriginalIntegerTiling318
public section
noncomputable section
namespace ActualOriginalFourierTiling318
open QuadricCRTAssembly318 ActualOriginalTwistedWeight318
open ActualOriginalCoordinateFrequency318 ActualOriginalIntegerTiling318 MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- The literal original Fourier integrand at an unrestricted full
coordinate frequency. -/
@[expose] def originalFourierIntegrand (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (y : Coordinates ℝ) (x : Coordinates ℝ) : ℂ :=
  Real.fourierChar (-frequency y x) • twistedWeight κ β W x

lemma actual_fourier_integrand_continuous (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (y : Coordinates ℝ) :
    Continuous (originalFourierIntegrand κ β W y) :=
  (Real.continuous_fourierChar.comp (frequency y).continuous.neg).smul
    (actual_twisted_weight_smooth κ β W hW).continuous

lemma actual_fourier_integrand_compact (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hWc : HasCompactSupport W) (y : Coordinates ℝ) :
    HasCompactSupport (originalFourierIntegrand κ β W y) :=
  (actual_twisted_weight_compact κ β W hWc).smul_left

lemma actual_fourier_integrand_integrable (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (y : Coordinates ℝ) :
    Integrable (originalFourierIntegrand κ β W y) :=
  (actual_fourier_integrand_continuous κ β W hW y).integrable_of_hasCompactSupport
    (actual_fourier_integrand_compact κ β W hWc y)

/-- Exact Fourier coefficient tiling BEFORE moving a countable sum
inside an integral. Every translated term keeps the actual full phase.
No unproved sum/integral exchange or periodicity premise is used. -/
theorem actual_original_fourier_tiling (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (y : Coordinates ℝ) :
    originalCoordinateFourier κ β W y =
      ∑' z : Coordinates ℤ, ∫ x in originalCube,
        originalFourierIntegrand κ β W y (integerEmbed z+x) :=
  actual_original_integral_tiling _ (actual_fourier_integrand_integrable κ β W hW hWc y)

end ActualOriginalFourierTiling318
