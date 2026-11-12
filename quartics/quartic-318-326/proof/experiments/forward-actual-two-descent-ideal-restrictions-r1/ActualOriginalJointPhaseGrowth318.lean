module
public import ActualOriginalCompleteSumBound318
public import Mathlib.Analysis.Distribution.TemperateGrowth
public section
noncomputable section
namespace ActualOriginalJointPhaseGrowth318
open QuadricCRTAssembly318 ActualOriginalCoordinateFrequency318 ActualOriginalTwistedWeight318
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- Joint parameter/source function with exactly the original positive
quadratic phase and original compact weight. -/
@[expose] def jointTwisted (κ : ℝ) (W : Coordinates ℝ → ℝ) (z : ℝ × Coordinates ℝ) : ℂ :=
  twistedWeight κ z.1 W z.2

lemma actual_equation_temperate (κ : ℝ) : Function.HasTemperateGrowth (equation κ : Coordinates ℝ → ℝ) := by
  have ha := pA.hasTemperateGrowth.pow 2
  have hb := pB.hasTemperateGrowth.pow 2
  have hc := pC.hasTemperateGrowth.pow 2
  have hd := pD.hasTemperateGrowth.pow 2
  have hw := pW.hasTemperateGrowth.pow 2
  simpa only [equation,pA,pB,pC,pD,pW,Function.comp_def,Pi.add_apply,Pi.sub_apply,
    Pi.mul_apply,Pi.pow_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst_apply,
    ContinuousLinearMap.snd_apply] using
      ((ha.add hb).sub (hc.add hd)).sub ((Function.HasTemperateGrowth.const κ).mul hw)

/-- The polynomial phase composed with exp(i*t) and the actual smooth
compact weight have joint temperate growth. Thus no fixed-beta constant is
silently used as a uniform constant. -/
theorem actual_joint_twisted_temperate (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    Function.HasTemperateGrowth (jointTwisted κ W) := by
  have hp := (ContinuousLinearMap.fst ℝ ℝ (Coordinates ℝ)).hasTemperateGrowth
  have hx := (ContinuousLinearMap.snd ℝ ℝ (Coordinates ℝ)).hasTemperateGrowth
  have hq := (actual_equation_temperate κ).comp hx
  have ht := ((Function.HasTemperateGrowth.const (2*Real.pi)).mul hp).mul hq
  have he := Complex.hasTemperateGrowth_exp_mul_I.comp ht
  have hw := Complex.hasTemperateGrowth_ofReal.comp ((hWc.hasTemperateGrowth hW).comp hx)
  exact hw.mul he

/-- Joint derivative control holds for all real beta and all original
source points, with one polynomial exponent and constant up to order n. -/
theorem actual_joint_twisted_derivative_bound (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j ≤ n, ∀ z : ℝ × Coordinates ℝ,
      ‖iteratedFDeriv ℝ j (jointTwisted κ W) z‖ ≤ C*(1+‖z‖)^k :=
  (actual_joint_twisted_temperate κ W hW hWc).norm_iteratedFDeriv_le_uniform n

end ActualOriginalJointPhaseGrowth318
