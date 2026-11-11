module
public import ActualOriginalJointPhaseGrowth318
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public section
noncomputable section
namespace ActualOriginalParameterSliceDerivatives318
open QuadricCRTAssembly318 ActualOriginalJointPhaseGrowth318 ActualOriginalTwistedWeight318
open scoped ContDiff BigOperators
set_option maxHeartbeats 16000000

@[expose] def sourceInclusion : Coordinates ℝ →L[ℝ] ℝ × Coordinates ℝ :=
  ContinuousLinearMap.inr ℝ ℝ (Coordinates ℝ)

lemma actual_source_inclusion_norm : ‖sourceInclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound zero_le_one
  intro x
  simp [sourceInclusion,Prod.norm_def]

/-- Actual partial source derivatives are joint derivatives composed
with the SAME norm-one source inclusion. Translation changes no derivative. -/
lemma actual_parameter_slice_derivative (F : ℝ × Coordinates ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (β : ℝ) (n : ℕ) (x : Coordinates ℝ) :
    iteratedFDeriv ℝ n (fun y : Coordinates ℝ => F (β,y)) x =
      (iteratedFDeriv ℝ n F (β,x)).compContinuousLinearMap (fun _ => sourceInclusion) := by
  let G : ℝ × Coordinates ℝ → ℂ := fun z => F ((β,0)+z)
  have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_const.add contDiff_id)
  have he := sourceInclusion.iteratedFDeriv_comp_right hG x (i:=n) (by simp)
  simpa [G,Function.comp_def,iteratedFDeriv_comp_add_left,sourceInclusion] using he

lemma actual_parameter_slice_norm_le (F : ℝ × Coordinates ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (β : ℝ) (n : ℕ) (x : Coordinates ℝ) :
    ‖iteratedFDeriv ℝ n (fun y : Coordinates ℝ => F (β,y)) x‖ ≤
      ‖iteratedFDeriv ℝ n F (β,x)‖ := by
  rw [actual_parameter_slice_derivative F hF β n x]
  have h := (iteratedFDeriv ℝ n F (β,x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => sourceInclusion)
  have hp : ‖sourceInclusion‖^n ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) actual_source_inclusion_norm
  calc
    _ ≤ ‖iteratedFDeriv ℝ n F (β,x)‖ * ‖sourceInclusion‖^n := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _)

/-- A common polynomial beta/source bound for every actual twisted
source derivative up to n, obtained from joint temperate growth. -/
theorem actual_twisted_source_derivative_bound (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j ≤ n, ∀ β : ℝ, ∀ x : Coordinates ℝ,
      ‖iteratedFDeriv ℝ j (twistedWeight κ β W) x‖ ≤ C*(1+‖(β,x)‖)^k := by
  obtain ⟨k,C,hC,hbound⟩ := actual_joint_twisted_derivative_bound κ W hW hWc n
  refine ⟨k,C,hC,fun j hj β x => ?_⟩
  exact (actual_parameter_slice_norm_le (jointTwisted κ W)
    (actual_joint_twisted_temperate κ W hW hWc).1 β j x).trans (hbound j hj (β,x))

end ActualOriginalParameterSliceDerivatives318
