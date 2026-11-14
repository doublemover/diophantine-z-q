module
public import ActualOriginalReciprocalDistance318
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Const
public section
noncomputable section
namespace ActualOriginalSmoothGlobalBounds318
open QuadricCRTAssembly318
open scoped ContDiff

/-- Compact support and continuity produce a GLOBAL norm bound,
including points outside the support, not just a bound on a chosen slice. -/
lemma actual_compact_global_bound {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] (f : E → F) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ A : ℝ, 0≤A ∧ ∀ x, ‖f x‖≤A := by
  obtain ⟨A,hA⟩ := hc.isCompact.bddAbove_image hf.norm.continuousOn
  refine ⟨max 0 A,le_max_left _ _,fun x => ?_⟩
  by_cases hx : x∈tsupport f
  · exact (hA ⟨x,hx,rfl⟩).trans (le_max_right _ _)
  · have hz : f x=0 := by
      by_contra hn
      exact hx (subset_tsupport f hn)
    rw [hz,norm_zero]
    exact le_max_left _ _

/-- The actual smooth compact original weight supplies its own amplitude
and global first-derivative constants. These are independent of scale,
base point, displacement and direction. -/
theorem actual_smooth_global_bounds (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L : ℝ, 0≤A ∧ 0≤L ∧ (∀ x, ‖W x‖≤A) ∧
      (∀ x y, ‖W x-W y‖≤L*‖x-y‖) := by
  obtain ⟨A,hA,ha⟩ := actual_compact_global_bound W hW.continuous hc
  obtain ⟨L,hL,hl⟩ := actual_compact_global_bound (fderiv ℝ W)
    (hW.continuous_fderiv (by simp)) (hc.fderiv ℝ)
  refine ⟨A,L,hA,hL,ha,fun x y => ?_⟩
  exact (convex_univ : Convex ℝ (Set.univ : Set (Coordinates ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hW.differentiable (by simp) z) (fun z _ => hl z)
    (Set.mem_univ y) (Set.mem_univ x)

end ActualOriginalSmoothGlobalBounds318
