module
public import PELUnlevelledComplexBase318
public import ComplexHolomorphicChartInverse318
public import RiemannChartDerivative318
public section
noncomputable section
namespace PELOriginalChartUniformizer318
open Set Filter HolomorphicQuotientCoverCharts318 HolomorphicQuotientCoverMaps318
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELPrincipalBaseHolomorphy318 PELUnlevelledComplexBase318 PELEffectiveNormOneAction318
open scoped Topology Manifold ContDiff
local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

variable (e : OpenPartialHomeomorph UnlevelledBase ℂ) (p : UnlevelledBase)
  (hp : p ∈ e.source) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
  (τ : HalfPlane) (hτ : projection τ = p)

@[expose] def transition : OpenPartialHomeomorph ℂ ℂ :=
  e.symm.trans (quotientChart projection covering τ)
@[expose] def uniformizer (z : ℂ) : ℂ := transition e τ (e p + z)

include hp hτ in
lemma transition_source : e p ∈ (transition e τ).source := by
  refine ⟨e.map_source hp,?_⟩
  rw [e.left_inv hp,←hτ]
  exact quotientChart_center projection covering τ

include hp hτ in
lemma transition_value : transition e τ (e p) = (τ : ℂ) := by
  change quotientChart projection covering τ (e.symm (e p)) = _
  rw [e.left_inv hp,←hτ,quotientChart_center_value]
  rfl

include hp he hτ in
lemma transition_analytic : AnalyticAt ℂ (transition e τ) (e p) := by
  have hq := contMDiffAt_of_mem_maximalAtlas
    (quotientChart_maximal projection covering effective_holomorphic τ)
    (quotientChart_center projection covering τ)
  have hq' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (quotientChart projection covering τ) (e.symm (e p)) := by
    simpa only [e.left_inv hp,←hτ] using hq
  exact (contMDiffAt_iff_contDiffAt.mp
    (hq'.comp (e p) (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)))).analyticAt

include hp he hτ in
lemma uniformizer_analytic : AnalyticAt ℂ (uniformizer e p τ) 0 := by
  have ht := transition_analytic e p hp he τ hτ
  have ht' : AnalyticAt ℂ (transition e τ) (e p + (0 : ℂ)) := by simpa using ht
  exact ht'.comp (analyticAt_const.add analyticAt_id : AnalyticAt ℂ (fun z : ℂ => e p + z) 0)

include hp hτ in
lemma uniformizer_zero : uniformizer e p τ 0 = (τ : ℂ) := by
  simpa only [uniformizer,add_zero] using transition_value e p hp τ hτ

include hp he hτ in
lemma uniformizer_noncritical : deriv (uniformizer e p τ) 0 ≠ 0 := by
  have ht := transition_analytic e p hp he τ hτ
  have hs := transition_source e p hp τ hτ
  have hn := RiemannChartDerivative318.derivative_ne_zero (transition e τ) hs ht
    (ComplexHolomorphicChartInverse318.inverse_analytic _ hs ht)
  have ht' : AnalyticAt ℂ (transition e τ) (e p + (0 : ℂ)) := by simpa using ht
  have hd := ht'.differentiableAt.hasDerivAt.comp 0
    ((hasDerivAt_const 0 (e p)).add (hasDerivAt_id 0))
  have hv : deriv (uniformizer e p τ) 0 = deriv (transition e τ) (e p) := by
    simpa only [uniformizer,add_zero,zero_add,mul_one] using hd.deriv
  rw [hv]
  exact hn

include hp hτ in
/-- The literal original covering projection recovers the given chart,
not merely an abstract analytic disk with the same center. -/
lemma projection_uniformizer : ∀ᶠ z in 𝓝 (0 : ℂ),
    0 < (uniformizer e p τ z).im ∧
    projection (baseChart.symm (uniformizer e p τ z)) = e.symm (e p + z) := by
  have hs := transition_source e p hp τ hτ
  have hc : ContinuousAt (fun z : ℂ => e p + z) 0 := continuousAt_const.add continuousAt_id
  have hn := hc.eventually (by simpa only [add_zero] using (transition e τ).open_source.mem_nhds hs)
  filter_upwards [hn] with z hz
  have hq := hz.2
  have ht := (quotientChart projection covering τ).map_source hq
  constructor
  · exact ht.1
  · have hi := (quotientChart projection covering τ).left_inv hq
    rw [quotientChart_symm] at hi
    exact hi

/-- Every actual original chart has a produced upper-half-plane
uniformizer with nonzero derivative and the exact covering square. -/
theorem exists_uniformizer (e : OpenPartialHomeomorph UnlevelledBase ℂ) (p : UnlevelledBase)
    (hp : p ∈ e.source) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ 0 < (f 0).im ∧ deriv f 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), 0 < (f z).im ∧
        projection (baseChart.symm (f z)) = e.symm (e p + z) := by
  obtain ⟨τ,hτ⟩ := projection_surjective p
  refine ⟨uniformizer e p τ,uniformizer_analytic e p hp he τ hτ,?_,
    uniformizer_noncritical e p hp he τ hτ,projection_uniformizer e p hp τ hτ⟩
  rw [uniformizer_zero e p hp τ hτ]
  exact τ.property
end PELOriginalChartUniformizer318
