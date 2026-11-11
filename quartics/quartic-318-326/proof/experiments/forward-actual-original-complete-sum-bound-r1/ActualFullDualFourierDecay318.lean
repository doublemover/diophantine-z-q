module
public import ActualOriginalLocalFourierProduct318
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Bilinear
public section
noncomputable section
namespace ActualFullDualFourierDecay318
open MeasureTheory
open scoped ContDiff BigOperators
set_option maxHeartbeats 16000000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] [MeasureSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- The actual dual evaluation pairing, without replacing the given norm
or its Haar measure by an inner-product model. -/
@[expose] def dualPairing : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.apply ℝ ℝ

@[expose] def dualFourier (f : SchwartzMap E ℂ) (ξ : E →L[ℝ] ℝ) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume dualPairing.toLinearMap₁₂ f ξ

/-- Compactness of the original unit sphere produces the actual norming
vector for every full dual frequency, including the zero functional. -/
lemma actual_dual_norming_vector (ξ : E →L[ℝ] ℝ) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖ξ v‖ = ‖ξ‖ := by
  obtain ⟨u,hu⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  have hs : (Metric.sphere (0 : E) 1).Nonempty :=
    ⟨u,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
  obtain ⟨v,hv,hm⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hs
    ξ.continuous.norm.continuousOn
  have hv1 : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
  refine ⟨v,hv1,le_antisymm ?_ ?_⟩
  · simpa only [hv1,mul_one] using ξ.le_opNorm v
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro w hw
    exact hm (by simpa only [Metric.mem_sphere,dist_zero_right] using hw)

/-- All polynomial decay orders in the FULL dual norm. The bound uses
weighted derivatives of the literal input; no normal-frequency restriction
or parameter-dependent norm conversion is hidden in this statement. -/
theorem actual_full_dual_power_bound (f : SchwartzMap E ℂ) (n : ℕ) :
    ∃ C : ℝ, ∀ ξ : E →L[ℝ] ℝ, ‖ξ‖^n * ‖dualFourier f ξ‖ ≤ C := by
  let C : ℝ := (2 : ℝ)^n *
    ∑ p ∈ Finset.range 1 ×ˢ Finset.range (n+1),
      ∫ z : E, ‖z‖^p.1 * ‖iteratedFDeriv ℝ p.2 f z‖
  refine ⟨C,fun ξ => ?_⟩
  obtain ⟨v,hv,hξ⟩ := actual_dual_norming_vector ξ
  have hξabs : |ξ v| = ‖ξ‖ := by simpa only [Real.norm_eq_abs] using hξ
  have h := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (dualPairing (E:=E)) (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞)) (f.smooth ⊤)
    (fun k j _ _ => f.integrable_pow_mul_iteratedFDeriv volume k j)
    (k := 0) (n := n) (by simp) le_top v ξ
  simpa only [dualPairing,ContinuousLinearMap.apply_apply,hv,hξabs,
    norm_iteratedFDeriv_zero,pow_zero,one_pow,mul_one,one_mul,Nat.cast_zero,
    zero_mul,zero_add,dualFourier,C] using h

end ActualFullDualFourierDecay318
