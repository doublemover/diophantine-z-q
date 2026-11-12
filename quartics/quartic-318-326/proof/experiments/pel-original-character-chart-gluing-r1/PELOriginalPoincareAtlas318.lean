module
public import PELOriginalPoincareIndependence318
public section
noncomputable section
namespace PELOriginalPoincareAtlas318
open Set Filter
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELUnlevelledComplexBase318 PELOriginalChartUniformizer318
open PELOriginalPoincareIndependence318 MobiusPoincarePullback318
open scoped Topology Manifold ContDiff
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

lemma density_comp (f k : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f (k z)) (hk : DifferentiableAt ℂ k z) :
    density (fun w => f (k w)) z = density f (k z) * ‖deriv k z‖^2 := by
  have hd := hf.hasDerivAt.comp z hk.hasDerivAt
  simp only [density,hd.deriv,norm_mul,mul_pow]
  ring

@[expose] def coordinateChange (e d : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (z : ℂ) : ℂ := d (e.symm (e p + z)) - d p

lemma coordinateChange_zero (e d : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source) : coordinateChange e d p 0 = 0 := by
  simp only [coordinateChange,add_zero,e.left_inv hp,sub_self]

lemma coordinateChange_analytic (e d : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source) (hq : p ∈ d.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase) :
    AnalyticAt ℂ (coordinateChange e d p) 0 := by
  have hD : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω d (e.symm (e p)) := by
    rw [e.left_inv hp]
    exact contMDiffAt_of_mem_maximalAtlas hd hq
  have ha : AnalyticAt ℂ (fun z => d (e.symm z)) (e p) :=
    (contMDiffAt_iff_contDiffAt.mp
      (hD.comp (e p) (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)))).analyticAt
  have ha' : AnalyticAt ℂ (fun z => d (e.symm z)) (e p + (0 : ℂ)) := by simpa using ha
  exact (ha'.comp (analyticAt_const.add analyticAt_id)).sub analyticAt_const

/-- Genuine Poincare conformal transition law on EVERY actual original
chart overlap. The upper-half-plane comparison uses original covering
uniqueness; no invariant metric or overlap law is supplied as a premise. -/
theorem chart_transition (e d : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source) (hq : p ∈ d.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (τ σ : HalfPlane) (hτ : projection τ = p) (hσ : projection σ = p) :
    density (uniformizer e p τ) 0 = density (uniformizer d p σ) 0 *
      ‖deriv (coordinateChange e d p) 0‖^2 := by
  let k := coordinateChange e d p
  have hk0 : k 0 = 0 := coordinateChange_zero e d p hp
  have hk : AnalyticAt ℂ k 0 := coordinateChange_analytic e d p hp hq he hd
  have hdf := uniformizer_analytic d p hq hd σ hσ
  have hdf' : AnalyticAt ℂ (uniformizer d p σ) (k 0) := by rwa [hk0]
  have hcomp : AnalyticAt ℂ (fun z => uniformizer d p σ (k z)) 0 := hdf'.comp hk
  have hupE : 0 < (uniformizer e p τ 0).im := by
    rw [uniformizer_zero e p hp τ hτ];exact τ.property
  have hupD : 0 < (uniformizer d p σ (k 0)).im := by
    rw [hk0,uniformizer_zero d p hq σ hσ];exact σ.property
  have hevent := projection_uniformizer e p hp τ hτ
  have hdevent : ∀ᶠ z in 𝓝 (0 : ℂ),
      0 < (uniformizer d p σ (k z)).im ∧
      projection (baseChart.symm (uniformizer d p σ (k z))) = d.symm (d p + k z) :=
    hk.continuousAt.eventually (by rw [hk0];exact projection_uniformizer d p hq σ hσ)
  have hinv : ContinuousAt (fun z : ℂ => e.symm (e p + z)) 0 := by
    have hv : e p + (0 : ℂ) ∈ e.target := by simpa using e.map_source hp
    exact (e.continuousAt_symm hv).comp (continuousAt_const.add continuousAt_id)
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), e.symm (e p + z) ∈ d.source :=
    hinv.eventually (by simpa only [add_zero,e.left_inv hp] using d.open_source.mem_nhds hq)
  have heq := density_eq_of_lifts _ _ (uniformizer_analytic e p hp he τ hτ)
    hcomp hupE hupD (by
      filter_upwards [hevent,hdevent,hnear] with z hz hw hv
      rw [hz.2,hw.2]
      have hvk : d p + k z = d (e.symm (e p + z)) := by dsimp [k,coordinateChange];ring
      rw [hvk,d.left_inv hv])
  rw [density_comp _ k 0 hdf'.differentiableAt hk.differentiableAt,hk0] at heq
  exact heq

@[expose] def chartDensity (e : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) : ℝ :=
  density (uniformizer e p (projection_surjective p).choose) 0

lemma chartDensity_positive (e : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase) :
    0 < chartDensity e p := by
  let τ := (projection_surjective p).choose
  have ht : projection τ = p := (projection_surjective p).choose_spec
  exact (density_positive_continuous _ (uniformizer_analytic e p hp he τ ht)
    (by rw [uniformizer_zero e p hp τ ht];exact τ.property)
    (uniformizer_noncritical e p hp he τ ht)).1

/-- The independently produced positive coefficients satisfy the full
actual cotangent metric cocycle. This is not yet the source/global-ratio comparison. -/
lemma chartDensity_transition (e d : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source) (hq : p ∈ d.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase) :
    chartDensity e p = chartDensity d p * ‖deriv (coordinateChange e d p) 0‖^2 :=
  chart_transition e d p hp hq he hd _ _
    (projection_surjective p).choose_spec (projection_surjective p).choose_spec
end PELOriginalPoincareAtlas318
