module
public import PELOriginalPoincareAtlas318
public section
noncomputable section
namespace PELOriginalPoincareContinuity318
open Set Filter HolomorphicQuotientCoverCharts318 HolomorphicQuotientCoverMaps318
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELUnlevelledComplexBase318 PELEffectiveNormOneAction318
open PELOriginalChartUniformizer318 PELOriginalPoincareAtlas318
open PELOriginalPoincareIndependence318 MobiusPoincarePullback318
open scoped Topology Manifold ContDiff
local instance : ChartedSpace ℂ HalfPlane := PELPrincipalBaseHolomorphy318.halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := PELPrincipalBaseHolomorphy318.halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

lemma fixed_analytic (e : OpenPartialHomeomorph UnlevelledBase ℂ) (p : UnlevelledBase)
    (hp : p ∈ e.source) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (τ : HalfPlane) (hq : p ∈ (quotientChart projection covering τ).source) :
    AnalyticAt ℂ (transition e τ) (e p) := by
  have hD : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (quotientChart projection covering τ) (e.symm (e p)) := by
    rw [e.left_inv hp]
    exact contMDiffAt_of_mem_maximalAtlas
      (quotientChart_maximal projection covering effective_holomorphic τ) hq
  exact (contMDiffAt_iff_contDiffAt.mp
    (hD.comp (e p) (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)))).analyticAt

lemma fixed_projection (e : OpenPartialHomeomorph UnlevelledBase ℂ) (p : UnlevelledBase)
    (hp : p ∈ e.source) (τ : HalfPlane)
    (hq : p ∈ (quotientChart projection covering τ).source) :
    ∀ᶠ z in 𝓝 (0 : ℂ), 0 < (uniformizer e p τ z).im ∧
      projection (baseChart.symm (uniformizer e p τ z)) = e.symm (e p + z) := by
  have hs : e p ∈ (transition e τ).source := ⟨e.map_source hp,by rwa [e.left_inv hp]⟩
  have hc : ContinuousAt (fun z : ℂ => e p + z) 0 := continuousAt_const.add continuousAt_id
  have hn := hc.eventually (by simpa only [add_zero] using (transition e τ).open_source.mem_nhds hs)
  filter_upwards [hn] with z hz
  have ht := (quotientChart projection covering τ).map_source hz.2
  refine ⟨ht.1,?_⟩
  have hi := (quotientChart projection covering τ).left_inv hz.2
  rw [quotientChart_symm] at hi
  exact hi

/-- The pointwise representative choice agrees locally with ONE fixed
analytic covering sheet. This is the needed continuity bridge, rather
than an assumption that arbitrary choices vary continuously. -/
lemma chartDensity_eq_fixed (e : OpenPartialHomeomorph UnlevelledBase ℂ) (p : UnlevelledBase)
    (hp : p ∈ e.source) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (τ : HalfPlane) (hq : p ∈ (quotientChart projection covering τ).source) :
    chartDensity e p = density (transition e τ) (e p) := by
  let σ := (projection_surjective p).choose
  have hσ : projection σ = p := (projection_surjective p).choose_spec
  have hf := fixed_analytic e p hp he τ hq
  have hf' : AnalyticAt ℂ (transition e τ) (e p + (0 : ℂ)) := by simpa using hf
  have hg : AnalyticAt ℂ (uniformizer e p τ) 0 :=
    hf'.comp (analyticAt_const.add analyticAt_id)
  have hupper : 0 < (uniformizer e p τ 0).im :=
    (fixed_projection e p hp τ hq).self_of_nhds.1
  have hd := density_eq_of_lifts _ _ (uniformizer_analytic e p hp he σ hσ) hg
    (by rw [uniformizer_zero e p hp σ hσ];exact σ.property) hupper (by
      filter_upwards [projection_uniformizer e p hp σ hσ,fixed_projection e p hp τ hq]
        with z hz hw
      exact hz.2.trans hw.2.symm)
  have hder := hf'.differentiableAt.hasDerivAt.comp 0
    ((hasDerivAt_const 0 (e p)).add (hasDerivAt_id 0))
  have hv : deriv (uniformizer e p τ) 0 = deriv (transition e τ) (e p) := by
    simpa only [uniformizer,add_zero,zero_add,mul_one] using hder.deriv
  change chartDensity e p = density (uniformizer e p τ) 0 at hd
  rw [density,hv,uniformizer,add_zero] at hd
  exact hd

/-- Actual positive hyperbolic coefficients are continuous on every full
original chart, with all discontinuous representative choices removed. -/
theorem chartDensity_continuousOn (e : OpenPartialHomeomorph UnlevelledBase ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase) :
    ContinuousOn (chartDensity e) e.source := by
  intro p hp
  obtain ⟨τ,hτ⟩ := projection_surjective p
  have hq : p ∈ (quotientChart projection covering τ).source := by
    rw [←hτ];exact quotientChart_center projection covering τ
  have hf := fixed_analytic e p hp he τ hq
  have hu : 0 < (transition e τ (e p)).im := by
    rw [transition_value e p hp τ hτ];exact τ.property
  have hc : ContinuousAt (density (transition e τ)) (e p) :=
    (hf.deriv.continuousAt.norm.pow 2).div
      ((Complex.continuous_im.continuousAt.comp hf.continuousAt).pow 2)
      (pow_ne_zero 2 hu.ne')
  apply ContinuousAt.continuousWithinAt
  apply (hc.comp (e.continuousAt hp)).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp,
    (quotientChart projection covering τ).open_source.mem_nhds hq] with q heq hqq
  exact chartDensity_eq_fixed e q heq he τ hqq
end PELOriginalPoincareContinuity318
