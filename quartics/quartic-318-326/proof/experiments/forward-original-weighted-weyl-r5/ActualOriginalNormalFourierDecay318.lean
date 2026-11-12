module
public import ActualOriginalFiniteRationalArc318
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public section
noncomputable section
namespace ActualOriginalNormalFourierDecay318
open ActualOriginalNormalLevelChart318 ActualOriginalPositiveQuadricChart318
open MeasureTheory
open scoped FourierTransform Real ContDiff BigOperators
set_option maxHeartbeats 16000000

/-- The original normal parameter paired with its real frequency; the
four remaining coordinates are integrated with their ORIGINAL volume. -/
@[expose] def normalPairing : LevelParameters →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ Parameters)

lemma normalPairing_apply (z : LevelParameters) (t : ℝ) : normalPairing z t = z.1*t := rfl

@[expose] def normalFourier (f : SchwartzMap LevelParameters ℂ) (t : ℝ) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume normalPairing.toLinearMap₁₂ f t

lemma normalFourier_continuous (f : SchwartzMap LevelParameters ℂ) :
    Continuous (normalFourier f) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (normalFourier f) :=
    VectorFourier.contDiff_fourierIntegral normalPairing
      (fun n _ => f.integrable_pow_mul volume n)
  exact h.continuous

/-- Actual polynomial decay of the Fourier transform along the original
normal direction. No inner-product norm is imposed on the original product
space: the pinned bilinear Fourier theorem is applied directly. -/
theorem normalFourier_power_bound (f : SchwartzMap LevelParameters ℂ) (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖t‖^n * ‖normalFourier f t‖ ≤ C := by
  let v : LevelParameters := (1,0)
  have hn : ‖v‖ = 1 := by simp [v,Prod.norm_def]
  let C : ℝ := (2 : ℝ)^n *
    ∑ p ∈ Finset.range 1 ×ˢ Finset.range (n+1),
      ∫ z : LevelParameters, ‖z‖^p.1 * ‖iteratedFDeriv ℝ p.2 f z‖
  refine ⟨C,fun t => ?_⟩
  have h := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    normalPairing (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞)) (f.smooth ⊤)
    (fun k j _ _ => f.integrable_pow_mul_iteratedFDeriv volume k j)
    (k := 0) (n := n) (by simp) le_top v t
  have hv : normalPairing v t = t := by simp [normalPairing_apply,v]
  simpa only [hv,hn,norm_iteratedFDeriv_zero,
    Real.norm_eq_abs,pow_zero,one_pow,mul_one,one_mul,Nat.cast_zero,
    zero_mul,zero_add,normalFourier,C] using h

/-- Absolute integrability on the WHOLE real frequency line follows
from produced polynomial bounds, not from Abel regularization. -/
theorem normalFourier_integrable (f : SchwartzMap LevelParameters ℂ) :
    Integrable (normalFourier f) := by
  obtain ⟨C0,h0⟩ := normalFourier_power_bound f 0
  obtain ⟨Cn,hn⟩ := normalFourier_power_bound f (volume : Measure ℝ).integrablePower
  have hmeas := (normalFourier_continuous f).aestronglyMeasurable
  have hi := integrable_of_le_of_pow_mul_le (μ := (volume : Measure ℝ)) (k := 0)
    (by simpa only [pow_zero,one_mul] using h0)
    (by simpa only [zero_add] using hn) hmeas
  have hnorm : Integrable (fun t : ℝ => ‖normalFourier f t‖) := by
    simpa only [pow_zero,one_mul] using hi
  exact hnorm.mono' hmeas (Filter.Eventually.of_forall (fun _ => le_rfl))

end ActualOriginalNormalFourierDecay318
