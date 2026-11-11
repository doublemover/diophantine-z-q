module
public import PELOriginalMaximalCharts318
public import PELMaximalFiberCardinality318
public import Mathlib.Analysis.Analytic.Order
public section
noncomputable section
namespace PELOriginalRamifiedProjection318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318 PELOriginalMaximalCharts318
open PELOriginalBranchLabels318 PELCoarseInertiaCoordinate318 PELInertiaSquaredCoordinate318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1900000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
local instance : ChartedSpace ℂ MaximalBase := maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := maximal_manifold

/-- The actual source inertia coordinate belongs to its ORIGINAL
maximal atlas; the new target atlas is not substituted for the source. -/
theorem inertia_chart_maximal (τ : HalfPlane) :
    inertiaChart τ∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase := by
  apply (inertiaChart τ).mem_maximalAtlas_of_contMDiffOn
  · exact fun x hx => (chart_holomorphic τ x hx).contMDiffWithinAt
  · exact fun z hz => (chart_inverse_holomorphic τ z hz).contMDiffWithinAt

/-- At EVERY actual branch center there is an original source chart and
an actual target maximal chart in which the literal quotient projection is
z↦z² on a full neighborhood. The corresponding analytic order is exactly2. -/
theorem original_ramified_chart (i : Fin 5) (τ : HalfPlane)
    (hp : PELUnlevelledComplexBase318.projection τ∈fixedLocus i) :
    ∃ e : OpenPartialHomeomorph MaximalBase ℂ,
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω MaximalBase ∧
      PELOriginalMaximalQuotient318.projection (PELUnlevelledComplexBase318.projection τ)∈e.source ∧
      e (PELOriginalMaximalQuotient318.projection (PELUnlevelledComplexBase318.projection τ))=0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ),e (PELOriginalMaximalQuotient318.projection
        ((inertiaChart τ).symm z))=z^2) ∧
      analyticOrderAt (fun z : ℂ => e (PELOriginalMaximalQuotient318.projection
        ((inertiaChart τ).symm z))) 0=2 := by
  obtain ⟨U,e,hU,hpU,hs,hv,hh⟩ := exists_branch_chart i τ hp
  have he : OriginalChart e := ⟨U,hU,hs,hh⟩
  have hsource : PELOriginalMaximalQuotient318.projection
      (PELUnlevelledComplexBase318.projection τ)∈e.source := by
    rw [hs]
    exact ⟨PELUnlevelledComplexBase318.projection τ,hpU,rfl⟩
  have he0 : e (PELOriginalMaximalQuotient318.projection
      (PELUnlevelledComplexBase318.projection τ))=0 := by
    rw [hv _ hpU,squaredCoordinate,chart_center,pow_two,zero_mul]
  have ht0 : (0 : ℂ)∈(inertiaChart τ).target := by
    rw [←chart_center τ]
    exact (inertiaChart τ).map_source (chart_center_source τ)
  have hInv0 : (inertiaChart τ).symm 0=PELUnlevelledComplexBase318.projection τ := by
    rw [←chart_center τ]
    exact (inertiaChart τ).left_inv (chart_center_source τ)
  have ht : Tendsto (inertiaChart τ).symm (𝓝 (0 : ℂ))
      (𝓝 (PELUnlevelledComplexBase318.projection τ)) := by
    simpa only [hInv0] using ((inertiaChart τ).continuousAt_symm ht0).tendsto
  have hformula : ∀ᶠ z in 𝓝 (0 : ℂ),e (PELOriginalMaximalQuotient318.projection
      ((inertiaChart τ).symm z))=z^2 := by
    filter_upwards [ht.eventually (hU.mem_nhds hpU),
      (inertiaChart τ).open_target.mem_nhds ht0] with z hz hzt
    exact (hv _ hz).trans (actual_square_model τ z hzt)
  refine ⟨e,original_chart_maximal e he,hsource,he0,hformula,?_⟩
  rw [analyticOrderAt_congr hformula]
  simpa using (analyticOrderAt_pow (f:=(id : ℂ→ℂ)) (z₀:=0) analyticAt_id 2)

/-- The regular local model is the identity in original source and
actual target maximal charts, on a full neighborhood of the center. -/
theorem original_regular_chart (p : UnlevelledBase) (hp : p∉nontrivialStabilizerLocus) :
    ∃ e : OpenPartialHomeomorph MaximalBase ℂ,
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω MaximalBase ∧
      PELOriginalMaximalQuotient318.projection p∈e.source ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p),e (PELOriginalMaximalQuotient318.projection
        ((chartAt ℂ p).symm z))=z := by
  obtain ⟨U,e,hU,hpU,hs,hv,hh⟩ := PELRegularQuotientChart318.exists_regular_chart p hp
  have hsource : PELOriginalMaximalQuotient318.projection p∈e.source := by
    rw [hs]
    exact ⟨p,hpU,rfl⟩
  refine ⟨e,original_chart_maximal e ⟨U,hU,hs,hh⟩,hsource,?_⟩
  let A := chartAt ℂ p
  have hpA : p∈A.source := mem_chart_source ℂ p
  have ht : Tendsto A.symm (𝓝 (A p)) (𝓝 p) := by
    simpa only [A.left_inv hpA] using (A.continuousAt_symm (A.map_source hpA)).tendsto
  filter_upwards [ht.eventually (hU.mem_nhds hpU),
    A.open_target.mem_nhds (A.map_source hpA)] with z hz hzt
  exact (hv _ hz).trans (A.right_inv hzt)
/-- Exhaustive branch statement on the ACTUAL original source points.
Both displayed coordinates lie in their respective genuine maximal atlases. -/
theorem every_branch_chart (p : UnlevelledBase) (hp : p∈nontrivialStabilizerLocus) :
    ∃ (a : OpenPartialHomeomorph UnlevelledBase ℂ)
      (e : OpenPartialHomeomorph MaximalBase ℂ),
      a∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase ∧
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω MaximalBase ∧
      p∈a.source ∧ PELOriginalMaximalQuotient318.projection p∈e.source ∧
      a p=0 ∧ e (PELOriginalMaximalQuotient318.projection p)=0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ),e (PELOriginalMaximalQuotient318.projection (a.symm z))=z^2) ∧
      analyticOrderAt (fun z : ℂ => e (PELOriginalMaximalQuotient318.projection (a.symm z))) 0=2 := by
  obtain ⟨i,hi⟩ := (original_locus_union p).mp hp
  obtain ⟨τ,rfl⟩ := PELUnlevelledComplexBase318.projection_surjective p
  obtain ⟨e,he,hs,h0,hformula,horder⟩ := original_ramified_chart i τ hi
  exact ⟨inertiaChart τ,e,inertia_chart_maximal τ,he,chart_center_source τ,hs,
    chart_center τ,h0,hformula,horder⟩
end PELOriginalRamifiedProjection318
