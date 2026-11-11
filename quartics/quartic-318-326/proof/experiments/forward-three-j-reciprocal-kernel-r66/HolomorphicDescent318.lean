module
public import ActualThreeCuspAssignment318
public import Mathlib.Analysis.Calculus.MeanValue
public section
noncomputable section
open Filter Topology Metric Set
namespace HolomorphicDescent318
set_option maxHeartbeats 0

/-- A holomorphic composite descends locally across a regular point of the
actual holomorphic map, using its genuine analytic inverse. -/
theorem analyticAt_of_comp_regular {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ (g ∘ f) z)
    (hd : deriv f z ≠ 0) : AnalyticAt ℂ g (f z) := by
  let r := hf.hasStrictDerivAt.localInverse _ _ _ hd
  have hr : AnalyticAt ℂ r (f z) := hf.analyticAt_localInverse hd
  have hr0 : r (f z) = z := HasStrictFDerivAt.localInverse_apply_image
    (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
  have ha : AnalyticAt ℂ ((g ∘ f) ∘ r) (f z) := (hr0.symm ▸ hg).comp hr
  apply ha.congr
  filter_upwards [HasStrictDerivAt.eventually_right_inverse
    (hf:=hf.hasStrictDerivAt) (hf':=hd)] with w hw
  exact congrArg g hw

/-- A nonconstant analytic germ has no critical points in a sufficiently small
punctured neighborhood. No unramifiedness at the center is required. -/
theorem eventually_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hn : ¬∀ᶠ w in 𝓝 z, f w=f z) :
    ∀ᶠ w in 𝓝[≠] z, deriv f w ≠ 0 := by
  rcases hf.deriv.eventually_eq_zero_or_eventually_ne_zero with hz | hne
  · exfalso
    apply hn
    have he := hf.eventually_analyticAt.and hz
    obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp he
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected
      (fun x hx => (hs hx).1.differentiableAt.differentiableWithinAt)
      (fun x hx => (hs hx).2) hw (mem_ball_self hr)
  · exact hne

/-- Holomorphic descent across all critical points of a nonconstant analytic
germ. Continuity at its image and holomorphicity of the pullback suffice. -/
theorem analyticAt_of_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hn : ¬∀ᶠ w in 𝓝 z, f w=f z)
    (hg : AnalyticAt ℂ (g ∘ f) z) (hc : ContinuousAt g (f z)) :
    AnalyticAt ℂ g (f z) := by
  have ho : 𝓝 (f z) ≤ Filter.map f (𝓝 z) :=
    hf.eventually_constant_or_nhds_le_map_nhds.resolve_left hn
  have hd := eventually_nhdsWithin_iff.mp (eventually_deriv_ne_zero hf hn)
  let s := {x : ℂ | AnalyticAt ℂ f x ∧ AnalyticAt ℂ (g ∘ f) x ∧
    (x ≠ z → deriv f x ≠ 0)}
  have hs : s ∈ 𝓝 z := by
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt,hd] with x hfx hgx hdx
    exact ⟨hfx,hgx,hdx⟩
  have hi : f '' s ∈ 𝓝 (f z) := ho (Filter.image_mem_map hs)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  have hi' : ∀ᶠ w in 𝓝 (f z), w ∈ f '' s := hi
  filter_upwards [hi'.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hne
  obtain ⟨x,hx,rfl⟩ := hw
  have hxne : x ≠ z := fun h => hne (congrArg f h)
  exact (analyticAt_of_comp_regular hx.1 hx.2.1 (hx.2.2 hxne)).differentiableAt

/-- Open analytic germ descent needs no separately assumed continuity of the
function downstairs: openness already forces it from pullback continuity. -/
theorem analyticAt_of_comp_nhds_le {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (ho : 𝓝 (f z) ≤ Filter.map f (𝓝 z))
    (hg : AnalyticAt ℂ (g ∘ f) z) : AnalyticAt ℂ g (f z) := by
  have hn : ¬∀ᶠ w in 𝓝 z, f w=f z := by
    intro hconst
    have he : ∀ᶠ w in 𝓝 (f z), w=f z := ho hconst
    have hfalse : ∀ᶠ w in 𝓝[≠] (f z), False := by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hnw
      exact hnw hw
    obtain ⟨w,hw⟩ := hfalse.exists
    exact hw
  have hc : ContinuousAt g (f z) :=
    (show Tendsto g (Filter.map f (𝓝 z)) (𝓝 (g (f z))) from
      tendsto_map'_iff.mpr hg.continuousAt).mono_left ho
  exact analyticAt_of_comp hf hn hg hc

end HolomorphicDescent318
