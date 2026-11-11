module
public import ActualFullDualFourierDecay318
public section
noncomputable section
namespace ActualOriginalTwistedWeight318
open QuadricCRTAssembly318 ActualFullDualFourierDecay318 MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- Original positive circle-method phase, with its exact2pi convention. -/
@[expose] def twistedWeight (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (x : Coordinates ℝ) : ℂ :=
  (W x : ℂ) * Complex.exp ((2*Real.pi*β*equation κ x : ℝ)*Complex.I)

lemma actual_twisted_weight_smooth (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (twistedWeight κ β W) := by
  have hQ : ContDiff ℝ ∞ (equation κ : Coordinates ℝ → ℝ) := by
    unfold equation
    fun_prop
  unfold twistedWeight
  exact (Complex.ofRealCLM.contDiff.comp hW).mul
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul hQ)).mul contDiff_const).cexp

lemma actual_twisted_weight_compact (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hWc : HasCompactSupport W) : HasCompactSupport (twistedWeight κ β W) := by
  apply hWc.mono
  intro x hx hzero
  apply hx
  simp only [twistedWeight,hzero,Complex.ofReal_zero,zero_mul]

@[expose] def actualTwistedSchwartz (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    SchwartzMap (Coordinates ℝ) ℂ :=
  (actual_twisted_weight_compact κ β W hWc).toSchwartzMap
    (actual_twisted_weight_smooth κ β W hW)

/-- Exact original compact oscillatory Fourier integral, now with a
full linear frequency instead of only the normal frequency. -/
@[expose] def originalTwistedFourier (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (ξ : Coordinates ℝ →L[ℝ] ℝ) : ℂ :=
  ∫ x : Coordinates ℝ, Real.fourierChar (-ξ x) • twistedWeight κ β W x

lemma actual_twisted_fourier_identity (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (ξ : Coordinates ℝ →L[ℝ] ℝ) :
    originalTwistedFourier κ β W ξ = dualFourier (actualTwistedSchwartz κ β W hW hWc) ξ := rfl

/-- Every fixed real quadratic phase parameter has full dual rapid
decay. No uniformity in β or unproved minor-arc bound is asserted. -/
theorem actual_original_full_dual_decay (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ C : ℝ, ∀ ξ : Coordinates ℝ →L[ℝ] ℝ,
      ‖ξ‖^n * ‖originalTwistedFourier κ β W ξ‖ ≤ C := by
  simpa only [actual_twisted_fourier_identity κ β W hW hWc] using
    actual_full_dual_power_bound (actualTwistedSchwartz κ β W hW hWc) n

end ActualOriginalTwistedWeight318
