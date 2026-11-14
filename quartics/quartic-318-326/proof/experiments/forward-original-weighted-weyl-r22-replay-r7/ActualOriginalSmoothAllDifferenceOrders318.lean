module
public import ActualOriginalIteratedDifference318
public section
noncomputable section
namespace ActualOriginalSmoothAllDifferenceOrders318
open ActualOriginalIteratedDifference318 ActualOriginalSmoothGlobalBounds318
open scoped ContDiff

/-- At EVERY finite order the constant is produced from the original
smooth compact function before all points and step vectors. The induction
uses actual operator-valued fderiv, not a supplied higher derivative bound.
Type0 suffices for the original finite-dimensional real spaces and every
iterated continuous-linear-map codomain used in the construction. -/
theorem actual_smooth_all_difference_orders (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F],
    ∀ f : E → F, ContDiff ℝ ∞ f → HasCompactSupport f →
    ∃ C : ℝ, 0≤C ∧ ∀ us : List E, us.length=k → ∀ x,
      ‖mixedDifference f us x‖≤C*directionProduct us := by
  induction k with
  | zero =>
    intro F _ _ f hf hc
    obtain ⟨C,hC,hb⟩ := actual_compact_global_bound f hf.continuous hc
    refine ⟨C,hC,fun us hu x => ?_⟩
    have he : us=[] := List.length_eq_zero.mp hu
    subst us
    simpa only [mixedDifference,directionProduct,mul_one] using hb x
  | succ k ih =>
    intro F _ _ f hf hc
    have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
    obtain ⟨C,hC,hb⟩ := ih (E →L[ℝ] F) (fderiv ℝ f) hdf (hc.fderiv ℝ)
    refine ⟨C,hC,fun us hu x => ?_⟩
    cases us with
    | nil => simp at hu
    | cons u us =>
      have hlen : us.length=k := by simpa only [List.length_cons,Nat.succ.injEq] using hu
      have hdiff := actual_mixed_hasFDerivAt f (hf.differentiable (by simp)) us
      have hbound (z : E) : ‖fderiv ℝ (mixedDifference f us) z‖≤C*directionProduct us := by
        rw [(hdiff z).fderiv]
        exact hb us hlen z
      have hm := (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (hdiff z).differentiableAt) (fun z _ => hbound z)
        (Set.mem_univ x) (Set.mem_univ (x+u))
      simpa only [mixedDifference,directionProduct,add_sub_cancel_left,mul_assoc,mul_left_comm,mul_comm] using hm

end ActualOriginalSmoothAllDifferenceOrders318
