module
public import ActualOriginalUniformMixedPlaneVariation318
public section
noncomputable section
namespace ActualOriginalSmoothTwoAxisCancellation318
open QuadricCRTAssembly318 ActualOriginalCompactCircleCount318
open ActualOriginalUniformMixedPlaneVariation318 ActualOriginalTwoAxisSliceIdentity318
open ActualOriginalTwoAxisCancellation318 ActualOriginalRationalBlockReciprocalSum318
open ActualOriginalWeightedBlockReciprocalBudget318
open scoped ContDiff

/-- BOTH original directions now cancel with constants PRODUCED only
from the actual smooth compact weight, uniformly in all shifts and slices.
No supplied mixed-increment or Hessian bound remains in this consumer. -/
theorem actual_smooth_uniform_two_axis_cancellation (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L D : ℝ, 0≤A ∧ 0≤L ∧ 0≤D ∧
      ∀ B : ℝ, 0<B → ∀ R : ℝ, 0≤R → ∀ h : Coordinates ℤ,
      ∀ lo₀ lo₁ c d e : ℤ, ∀ N M : ℕ, (N : ℝ)≤R*B → (M : ℝ)≤R*B → ∀ t : ℝ,
      ‖originalPlaneCorrelation κ (latticeWeight B W) (t : AddCircle (1 : ℝ)) h
        lo₀ lo₁ c d e (N+1) (M+1)‖≤
        fourierChordCap ((N : ℝ)+1) (2*h.1.1) t*
          fourierChordCap ((M : ℝ)+1) (2*h.1.2) t*
            (A^2+4*R*A*L+R^2*(2*A*D+2*L^2)) := by
  obtain ⟨A,L,D,hA,hL,hD,hvar⟩ := actual_smooth_uniform_mixed_plane_variation W hW hc
  refine ⟨A,L,D,hA,hL,hD,fun B hB R hR h lo₀ lo₁ c d e N M hN hM t => ?_⟩
  apply (actual_original_two_axis_cancellation κ (latticeWeight B W) t h lo₀ lo₁ c d e N M).trans
  exact mul_le_mul_of_nonneg_left (hvar B hB R hR h lo₀ lo₁ c d e N M hN hM)
    (mul_nonneg (actual_chord_cap_nonneg _ _ _ (by positivity))
      (actual_chord_cap_nonneg _ _ _ (by positivity)))

end ActualOriginalSmoothTwoAxisCancellation318
