module
public import PELOriginalPoincareContinuity318
public section
noncomputable section
namespace PELOriginalPoincareLocalGerm318
open Set Filter HolomorphicQuotientCoverCharts318 HolomorphicQuotientCoverMaps318
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELUnlevelledComplexBase318 PELEffectiveNormOneAction318
open PELOriginalChartUniformizer318 PELOriginalPoincareAtlas318
open PELOriginalPoincareContinuity318 MobiusPoincarePullback318
open scoped Topology Manifold ContDiff
local instance : ChartedSpace ℂ HalfPlane := PELPrincipalBaseHolomorphy318.halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := PELPrincipalBaseHolomorphy318.halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- The globally representative-independent coefficient agrees on an
ENTIRE neighborhood with the derivative-weighted density of one fixed
actual covering sheet. This is the local metric identity needed by the
compact maximum-principle consumer, stronger than equality at the center. -/
theorem uniformizer_germ (e : OpenPartialHomeomorph UnlevelledBase ℂ) (p : UnlevelledBase)
    (hp : p ∈ e.source) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (τ : HalfPlane) (hτ : projection τ=p) :
    ∀ᶠ z in 𝓝 (0 : ℂ),chartDensity e (e.symm (e p+z))=density (uniformizer e p τ) z := by
  have hq : p ∈ (quotientChart projection covering τ).source := by
    rw [←hτ]
    exact quotientChart_center projection covering τ
  have ht : e p ∈ (transition e τ).source :=
    ⟨e.map_source hp,by rwa [e.left_inv hp]⟩
  have hn := (continuousAt_const.add continuousAt_id :
      ContinuousAt (fun z : ℂ => e p+z) 0).eventually
    (by simpa only [add_zero] using (transition e τ).open_source.mem_nhds ht)
  filter_upwards [hn] with z hz
  let q := e.symm (e p+z)
  have hqe : q ∈ e.source := e.map_target hz.1
  have hqτ : q ∈ (quotientChart projection covering τ).source := hz.2
  rw [chartDensity_eq_fixed e q hqe he τ hqτ,e.right_inv hz.1]
  have hf : AnalyticAt ℂ (transition e τ) (e p+z) := by
    simpa only [q,e.right_inv hz.1] using fixed_analytic e q hqe he τ hqτ
  have hd := hf.differentiableAt.hasDerivAt.comp z
    ((hasDerivAt_const z (e p)).add (hasDerivAt_id z))
  have hder : deriv (uniformizer e p τ) z=deriv (transition e τ) (e p+z) := by
    simpa only [uniformizer,zero_add,mul_one] using hd.deriv
  unfold density
  rw [hder]
  rfl
end PELOriginalPoincareLocalGerm318
