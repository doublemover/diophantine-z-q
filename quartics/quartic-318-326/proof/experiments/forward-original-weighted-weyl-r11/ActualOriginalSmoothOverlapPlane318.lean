module
public import ActualOriginalBoxPlaneAggregation318
public section
noncomputable section
namespace ActualOriginalSmoothOverlapPlane318
open QuadricCRTAssembly318 ActualOriginalCompactCircleCount318
open ActualOriginalBoxPlaneAggregation318 ActualOriginalCanonicalOverlapLength318
open ActualOriginalSmoothTwoAxisCancellation318 ActualOriginalTwoAxisCancellation318
open ActualOriginalRationalBlockReciprocalSum318 ActualOriginalWeightedBlockReciprocalBudget318
open scoped ContDiff

@[expose] def smoothPlaneCost (A L D R : ℝ) : ℝ :=
  A^2+4*R*A*L+R^2*(2*A*D+2*L^2)
lemma actual_smooth_plane_cost_nonneg (A L D R : ℝ)
    (hA : 0≤A) (hL : 0≤L) (hD : 0≤D) (hR : 0≤R) : 0≤smoothPlaneCost A L D R := by
  unfold smoothPlaneCost
  positivity
lemma actual_chord_cap_mono (N M : ℝ) (c : ℤ) (t : ℝ) (h : N≤M) :
    fourierChordCap N c t≤fourierChordCap M c t := by
  unfold fourierChordCap
  split_ifs
  · exact h
  · exact min_le_min h le_rfl

/-- Actual overlap planes, including BOTH empty-axis cases, have one
uniform majorant. No division by a zero length or nonresonance assumption. -/
theorem actual_smooth_overlap_plane_bound (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L D : ℝ, 0≤A ∧ 0≤L ∧ 0≤D ∧
      ∀ B R : ℝ, 0<B → 0≤R → ∀ H : ℤ, 0≤H → 2*(H : ℝ)+1≤R*B →
      ∀ h : Coordinates ℤ, ∀ c d e : ℤ, ∀ t : ℝ,
      ‖overlapPlaneCorrelation κ H (latticeWeight B W) (t : AddCircle (1 : ℝ)) h c d e‖≤
        fourierChordCap (2*(H : ℝ)+1) (2*h.1.1) t*
          fourierChordCap (2*(H : ℝ)+1) (2*h.1.2) t*smoothPlaneCost A L D R := by
  obtain ⟨A,L,D,hA,hL,hD,hall⟩ := actual_smooth_uniform_two_axis_cancellation κ W hW hc
  refine ⟨A,L,D,hA,hL,hD,fun B R hB hR H hH hsize h c d e t => ?_⟩
  have hN : (0 : ℝ)≤2*(H : ℝ)+1 := by exact_mod_cast (show (0 : ℤ)≤2*H+1 by omega)
  have hC := actual_smooth_plane_cost_nonneg A L D R hA hL hD hR
  have hn : (overlapLength H h.1.1 : ℝ)≤2*(H : ℝ)+1 := by
    exact_mod_cast actual_overlap_length_le H h.1.1 hH
  have hm : (overlapLength H h.1.2 : ℝ)≤2*(H : ℝ)+1 := by
    exact_mod_cast actual_overlap_length_le H h.1.2 hH
  rw [actual_overlap_plane_identity]
  cases en : overlapLength H h.1.1 with
  | zero =>
    simp only [actual_original_plane_empty_left,norm_zero]
    exact mul_nonneg (mul_nonneg (actual_chord_cap_nonneg _ _ _ hN)
      (actual_chord_cap_nonneg _ _ _ hN)) hC
  | succ n =>
    cases em : overlapLength H h.1.2 with
    | zero =>
      simp only [actual_original_plane_empty_right,norm_zero]
      exact mul_nonneg (mul_nonneg (actual_chord_cap_nonneg _ _ _ hN)
        (actual_chord_cap_nonneg _ _ _ hN)) hC
    | succ m =>
      have hn' : (n : ℝ)+1≤2*(H : ℝ)+1 := by simpa only [en,Nat.cast_succ] using hn
      have hm' : (m : ℝ)+1≤2*(H : ℝ)+1 := by simpa only [em,Nat.cast_succ] using hm
      have hb := hall B hB R hR h (max (-H) (-H-h.1.1))
        (max (-H) (-H-h.1.2)) c d e n m (by linarith) (by linarith) t
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ hC
      exact mul_le_mul (actual_chord_cap_mono _ _ _ _ hn')
        (actual_chord_cap_mono _ _ _ _ hm')
        (actual_chord_cap_nonneg _ _ _ (by positivity)) (actual_chord_cap_nonneg _ _ _ hN)

end ActualOriginalSmoothOverlapPlane318
