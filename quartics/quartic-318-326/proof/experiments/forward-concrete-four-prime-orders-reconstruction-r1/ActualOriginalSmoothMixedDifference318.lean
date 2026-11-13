module
public import ActualOriginalTwoAxisCancellation318
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public section
noncomputable section
namespace ActualOriginalSmoothMixedDifference318
open QuadricCRTAssembly318 ActualOriginalSmoothGlobalBounds318
open scoped ContDiff

/-- Smooth compact W produces a GLOBAL Lipschitz constant for its actual
first derivative. This constant is selected before translations or scales. -/
theorem actual_smooth_derivative_lipschitz (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ D : ℝ, 0≤D ∧ ∀ x y, ‖fderiv ℝ W x-fderiv ℝ W y‖≤D*‖x-y‖ := by
  have hDW : ContDiff ℝ ∞ (fderiv ℝ W) := (contDiff_infty_iff_fderiv.mp hW).2
  obtain ⟨D,hD,hd⟩ := actual_compact_global_bound (fderiv ℝ (fderiv ℝ W))
    (hDW.continuous_fderiv (by simp)) ((hc.fderiv ℝ).fderiv ℝ)
  refine ⟨D,hD,fun x y => ?_⟩
  exact (convex_univ : Convex ℝ (Set.univ : Set (Coordinates ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hDW.differentiable (by simp) z) (fun z _ => hd z)
    (Set.mem_univ y) (Set.mem_univ x)

/-- The mixed finite difference is bounded by the PRODUCT of step norms,
not by their sum. It follows from the actual derivative difference and a
second mean-value application, with no rectangle-specific constant. -/
theorem actual_mixed_difference_of_derivative_lipschitz
    (W : Coordinates ℝ → ℝ) (hW : Differentiable ℝ W) (D : ℝ)
    (hd : ∀ x y, ‖fderiv ℝ W x-fderiv ℝ W y‖≤D*‖x-y‖)
    (x u v : Coordinates ℝ) :
    ‖(W x-W (x+u))-(W (x+v)-W (x+v+u))‖≤D*‖u‖*‖v‖ := by
  let G : Coordinates ℝ → ℝ := fun z => W (z+u)-W z
  have hG (z : Coordinates ℝ) :
      HasFDerivAt G (fderiv ℝ W (z+u)-fderiv ℝ W z) z := by
    have hs := (hW (z+u)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const u)
    simpa only [ContinuousLinearMap.comp_id] using hs.sub (hW z).hasFDerivAt
  have hb (z : Coordinates ℝ) : ‖fderiv ℝ G z‖≤D*‖u‖ := by
    rw [(hG z).fderiv]
    simpa only [add_sub_cancel_left] using hd (z+u) z
  have hm := (convex_univ : Convex ℝ (Set.univ : Set (Coordinates ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hG z).differentiableAt) (fun z _ => hb z)
    (Set.mem_univ x) (Set.mem_univ (x+v))
  have he : (W x-W (x+u))-(W (x+v)-W (x+v+u))=G (x+v)-G x := by
    dsimp [G]
    ring
  rw [he]
  simpa only [add_sub_cancel_left] using hm

/-- One A,L,D supplies amplitude, first variation and genuine mixed
variation for the actual original weight at ALL points and step vectors. -/
theorem actual_smooth_mixed_constants (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L D : ℝ, 0≤A ∧ 0≤L ∧ 0≤D ∧ (∀ x, ‖W x‖≤A) ∧
      (∀ x y, ‖W x-W y‖≤L*‖x-y‖) ∧
      (∀ x u v, ‖(W x-W (x+u))-(W (x+v)-W (x+v+u))‖≤D*‖u‖*‖v‖) := by
  obtain ⟨A,L,hA,hL,ha,hl⟩ := actual_smooth_global_bounds W hW hc
  obtain ⟨D,hD,hd⟩ := actual_smooth_derivative_lipschitz W hW hc
  exact ⟨A,L,D,hA,hL,hD,ha,hl,fun x u v =>
    actual_mixed_difference_of_derivative_lipschitz W (hW.differentiable (by simp)) D hd x u v⟩

end ActualOriginalSmoothMixedDifference318
