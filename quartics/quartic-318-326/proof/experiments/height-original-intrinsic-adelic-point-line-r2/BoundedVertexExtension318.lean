module
public import ComplexCurveRemovablePoints318
public section
noncomputable section
namespace BoundedVertexExtension318
open Set Filter Function
open scoped Topology
set_option maxHeartbeats 1800000

/-- A bounded punctured holomorphic coordinate has a constructed analytic
extension. Continuity at the missing point is a conclusion, not an input. -/
theorem analytic_extension {f : ℂ → ℂ} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c,DifferentiableAt ℂ f z)
    (B : ℝ) (hb : ∀ᶠ z in 𝓝[≠] c,‖f z‖≤B) :
    ∃ g : ℂ → ℂ,AnalyticAt ℂ g c ∧ g =ᶠ[𝓝[≠] c] f ∧
      Tendsto f (𝓝[≠] c) (𝓝 (g c)) := by
  have hbound : IsBoundedUnder (·≤·) (𝓝[≠] c) (fun z => ‖f z-f c‖) := by
    refine ⟨B+‖f c‖,?_⟩
    change ∀ᶠ z in 𝓝[≠] c, ‖f z-f c‖ ≤ B+‖f c‖
    filter_upwards [hb] with z hz
    exact (norm_sub_le _ _).trans (add_le_add hz (le_refl ‖f c‖))
  have ht := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hbound
  let g : ℂ → ℂ := update f c (limUnder (𝓝[≠] c) f)
  have hc : ContinuousAt g c := continuousAt_update_same.mpr ht
  have hg : g =ᶠ[𝓝[≠] c] f := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [g,update_of_ne hz]
  have hdg : ∀ᶠ z in 𝓝[≠] c,DifferentiableAt ℂ g z := by
    filter_upwards [hd,self_mem_nhdsWithin] with z hz hzc
    apply hz.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hzc] with w hw
    simp only [g,update_of_ne hw]
  refine ⟨g,Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdg hc,hg,?_⟩
  simpa only [g,Function.update_self] using ht

/-- The genuine z−1/z coordinate is bounded by three on the inner
boundary collar. This is an affine bound, not compactness of the sphere. -/
theorem joukowski_bound (w : ℂ) (hlo : (1/2:ℝ)≤‖w‖) (hhi : ‖w‖≤1) :
    ‖w-w⁻¹‖≤3 := by
  have hp : 0<‖w‖ := lt_of_lt_of_le (by norm_num) hlo
  have hi : ‖w‖⁻¹≤2 := by
    simpa only [one_div,inv_inv] using
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hlo)
  calc ‖w-w⁻¹‖≤‖w‖+‖w⁻¹‖ := norm_sub_le _ _
       _=‖w‖+‖w‖⁻¹ := by rw [norm_inv]
       _≤3 := by linarith

/-- At a remaining isolated vertex, the actual bounded Joukowski
coordinate extends analytically once edge gluing has supplied its
punctured holomorphy. No boundary limit or continuity is postulated. -/
theorem joukowski_vertex_extension {f : ℂ → ℂ} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c,DifferentiableAt ℂ (fun w => f w-(f w)⁻¹) z)
    (hcollar : ∀ᶠ z in 𝓝[≠] c,(1/2:ℝ)≤‖f z‖ ∧ ‖f z‖≤1) :
    ∃ g : ℂ → ℂ,AnalyticAt ℂ g c ∧
      g =ᶠ[𝓝[≠] c] (fun w => f w-(f w)⁻¹) ∧
      Tendsto (fun w => f w-(f w)⁻¹) (𝓝[≠] c) (𝓝 (g c)) := by
  apply analytic_extension hd 3
  filter_upwards [hcollar] with z hz
  exact joukowski_bound (f z) hz.1 hz.2
end BoundedVertexExtension318
