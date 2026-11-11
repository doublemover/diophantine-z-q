module
public import RiemannChartDerivative318
public section
noncomputable section
namespace RiemannNormalizedInterior318
open Set Metric Filter Topology RiemannMappingBiholomorph318 RiemannChartDerivative318
set_option maxHeartbeats 2400000

/-- The normalized interior conformal chart has positive real derivative
at the selected original point. No orientation is chosen on a substituted
Klein or topological disk. -/
theorem exists_normalized_disk {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsSimplyConnected U) (hproper : U≠univ) {z₀ : ℂ} (hz₀ : z₀∈U) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source=U ∧ e.target=ball 0 1 ∧ e z₀=0 ∧
      (∀ z∈U,AnalyticAt ℂ e z) ∧ (∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w) ∧
      (deriv e z₀).im=0 ∧ 0<(deriv e z₀).re := by
  obtain ⟨e,hs,ht,hzero,he,hi⟩ := exists_biholomorphic_disk hU hconn hproper hz₀
  have hz : z₀∈e.source := hs.symm ▸ hz₀
  have hd : deriv e z₀≠0 := derivative_ne_zero e hz (he z₀ hz₀)
    (hi (e z₀) (ht ▸ e.map_source hz))
  let f : ℂ → ℂ := fun z => phase (deriv e z₀)*e z
  have hf : DifferentiableOn ℂ f U := by
    intro z hzu
    exact (differentiableAt_const.mul (he z hzu).differentiableAt).differentiableWithinAt
  have heb : BijOn e U (ball 0 1) := by
    rw [←hs,←ht]
    exact e.bijOn
  have hb : BijOn f U (ball 0 1) := (phase_disk_bijective _ hd).comp heb
  let hc := hconn.isPathConnected.isConnected.isPreconnected
  let hn : Nonempty U := ⟨⟨z₀,hz₀⟩⟩
  let e' := chart hU hc hn f hf hb
  have heq : EqOn e' f U := chart_eq hU hc hn f hf hb
  have hdz : HasDerivAt f (‖deriv e z₀‖:ℂ) z₀ := by
    have hh := (he z₀ hz₀).differentiableAt.hasDerivAt.const_mul (phase (deriv e z₀))
    rw [phase_mul _ hd] at hh
    exact hh
  have hde : deriv e' z₀=(‖deriv e z₀‖:ℂ) := by
    apply HasDerivAt.deriv
    apply hdz.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz₀] with z hzu
    exact heq hzu
  refine ⟨e',chart_source hU hc hn f hf hb,chart_target hU hc hn f hf hb,
    ?_,(chart_biholomorphic hU hc hn f hf hb).1,
    (chart_biholomorphic hU hc hn f hf hb).2,?_,?_⟩
  · rw [heq hz₀]
    simp only [f,hzero,mul_zero]
  · rw [hde]
    rfl
  · rw [hde]
    exact norm_pos_iff.mpr hd
end RiemannNormalizedInterior318
