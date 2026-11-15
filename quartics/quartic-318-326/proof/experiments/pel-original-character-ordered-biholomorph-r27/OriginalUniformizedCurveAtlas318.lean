module
public import PELOriginalPoincareLocalGerm318
public import HolomorphicHomeomorphChartTransport318
public import PELOriginalBaseCompact318
public section
noncomputable section
namespace OriginalUniformizedCurveAtlas318
open Set Filter
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318 PELUnlevelledComplexBase318
open PELOriginalChartUniformizer318 PELOriginalPoincareAtlas318 PELOriginalPoincareContinuity318
open MobiusPoincarePullback318
open scoped Topology Manifold ContDiff
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
  (H : UnlevelledBase ≃ₜ M)
  (hH : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H)
  (hI : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm)

@[expose] def sourceChart (e : OpenPartialHomeomorph M ℂ) : OpenPartialHomeomorph UnlevelledBase ℂ :=
  H.toOpenPartialHomeomorph.trans e
include hH hI in
lemma sourceChart_maximal (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    sourceChart H e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase :=
  HolomorphicHomeomorphChartTransport318.maximal H hH hI e he
lemma sourceChart_center (e : OpenPartialHomeomorph M ℂ) (p : M) (hp : p ∈ e.source) :
    H.symm p ∈ (sourceChart H e).source :=
  ⟨Set.mem_univ _,by simpa only [H.apply_symm_apply] using hp⟩
lemma sourceChart_value (e : OpenPartialHomeomorph M ℂ) (p : M) :
    sourceChart H e (H.symm p)=e p := by
  change e (H (H.symm p))=e p
  rw [H.apply_symm_apply]
lemma sourceChart_inverse (e : OpenPartialHomeomorph M ℂ) (z : ℂ) :
    (sourceChart H e).symm z=H.symm (e.symm z) := rfl

@[expose] def coefficient (e : OpenPartialHomeomorph M ℂ) (p : M) : ℝ :=
  chartDensity (sourceChart H e) (H.symm p)
include hH hI in
lemma coefficient_positive (e : OpenPartialHomeomorph M ℂ) (p : M) (hp : p ∈ e.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) : 0<coefficient H e p :=
  chartDensity_positive _ _ (sourceChart_center H e p hp) (sourceChart_maximal H hH hI e he)
include hH hI in
lemma coefficient_continuousOn (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    ContinuousOn (coefficient H e) e.source :=
  (chartDensity_continuousOn _ (sourceChart_maximal H hH hI e he)).comp
    H.symm.continuous.continuousOn (fun p hp => sourceChart_center H e p hp)

include hH hI in
/-- The exact whole-chart tensor-square cocycle is retained after the
actual original biholomorphic comparison. -/
theorem coefficient_transition (e d : OpenPartialHomeomorph M ℂ) (p : M)
    (hp : p ∈ e.source) (hq : p ∈ d.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    coefficient H e p=coefficient H d p *
      ‖deriv (fun z : ℂ => d (e.symm (e p+z))-d p) 0‖^2 := by
  have ht := chartDensity_transition (sourceChart H e) (sourceChart H d) (H.symm p)
    (sourceChart_center H e p hp) (sourceChart_center H d p hq)
    (sourceChart_maximal H hH hI e he) (sourceChart_maximal H hH hI d hd)
  have hk : coordinateChange (sourceChart H e) (sourceChart H d) (H.symm p)=
      (fun z : ℂ => d (e.symm (e p+z))-d p) := by
    funext z
    unfold coordinateChange
    rw [sourceChart_value,sourceChart_value,sourceChart_inverse]
    change d (H (H.symm (e.symm (e p+z))))-d p=_
    rw [H.apply_symm_apply]
  rw [hk] at ht
  exact ht

include hH hI in
/-- Actual chart uniformizer and actual neighborhood metric equality are
produced together through the fixed original arithmetic quotient. -/
theorem exists_uniformizer_with_metric (e : OpenPartialHomeomorph M ℂ) (p : M)
    (hp : p ∈ e.source) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ 0<(f 0).im ∧ deriv f 0≠0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ),0<(f z).im ∧
        H (projection (baseChart.symm (f z)))=e.symm (e p+z)) ∧
      (∀ᶠ z in 𝓝 (0 : ℂ),coefficient H e (e.symm (e p+z))=density f z) := by
  let E := sourceChart H e
  let q := H.symm p
  have hq : q ∈ E.source := sourceChart_center H e p hp
  have hE : E ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase :=
    sourceChart_maximal H hH hI e he
  obtain ⟨τ,hτ⟩ := projection_surjective q
  refine ⟨uniformizer E q τ,uniformizer_analytic E q hq hE τ hτ,?_,
    uniformizer_noncritical E q hq hE τ hτ,?_,?_⟩
  · rw [uniformizer_zero E q hq τ hτ]
    exact τ.property
  · filter_upwards [projection_uniformizer E q hq τ hτ] with z hz
    refine ⟨hz.1,?_⟩
    rw [hz.2,sourceChart_value,sourceChart_inverse,H.apply_symm_apply]
  · have hg := PELOriginalPoincareLocalGerm318.uniformizer_germ E q hq hE τ hτ
    simpa only [E,q,sourceChart_value,sourceChart_inverse,coefficient] using hg

include H in
/-- Compactness is inherited through the SAME map, not added separately. -/
theorem compactSpace : CompactSpace M := by
  apply isCompact_univ_iff.mp
  rw [←Set.range_eq_univ.mpr H.surjective,←Set.image_univ]
  exact isCompact_univ.image H.continuous
end OriginalUniformizedCurveAtlas318
