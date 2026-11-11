module
public import HolomorphicQuotientCoverCharts318
public section
noncomputable section
namespace HolomorphicQuotientCoverMaps318
open HolomorphicQuotientCoverCharts318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [TopologicalSpace Q] [Group G] [MulAction G M] [ContinuousConstSMul G M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ω M]
variable (q : M → Q) (hq : IsQuotientCoveringMap q G)
  (hhol : ∀ g : G, ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) ω (fun x : M => g • x))

include hhol in
theorem quotientChart_maximal (a : M) :
    letI := quotientCharts (E:=E) q hq
    quotientChart (E:=E) q hq a∈IsManifold.maximalAtlas 𝓘(ℂ,E) ω Q := by
  letI := quotientCharts (E:=E) q hq
  letI : IsManifold 𝓘(ℂ,E) ω Q := quotient_manifold q hq hhol
  exact IsManifold.subset_maximalAtlas ⟨a,rfl⟩

theorem quotientChart_center_value (a : M) :
    quotientChart (E:=E) q hq a (q a)=chartAt E a a := by
  rw [quotientChart_apply]
  congr 1
  exact hq.isLocalHomeomorph.localInverseAt_apply_self

include hhol in
/-- The exact covering projection is holomorphic for the constructed
quotient atlas, including at every original point of the covering space. -/
theorem projection_holomorphic :
    letI := quotientCharts (E:=E) q hq
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) ω q := by
  letI := quotientCharts (E:=E) q hq
  letI : IsManifold 𝓘(ℂ,E) ω Q := quotient_manifold q hq hhol
  intro a
  have hp := quotientChart_center (E:=E) q hq a
  have ht : chartAt E a a∈(quotientChart (E:=E) q hq a).target := by
    simpa only [quotientChart_center_value] using (quotientChart q hq a).map_source hp
  have hA := contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a)
    (mem_chart_source E a)
  have hB := contMDiffAt_symm_of_mem_maximalAtlas (quotientChart_maximal q hq hhol a) ht
  apply (hB.comp a hA).congr_of_eventuallyEq
  filter_upwards [(chartAt E a).open_source.mem_nhds (mem_chart_source E a)] with x hx
  change q x=(quotientChart (E:=E) q hq a).symm (chartAt E a x)
  rw [quotientChart_symm,(chartAt E a).left_inv hx]

variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ,F) ω N]

include hhol in
/-- Holomorphic descent through the actual covering, with the commuting
square required for ALL representatives and the literal descended map. -/
theorem descended_holomorphic (f : Q → N) (lift : M → N)
    (hlift : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ω lift) (hsquare : ∀ x, f (q x)=lift x) :
    letI := quotientCharts (E:=E) q hq
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ω f := by
  letI := quotientCharts (E:=E) q hq
  letI : IsManifold 𝓘(ℂ,E) ω Q := quotient_manifold q hq hhol
  intro p
  obtain ⟨a,rfl⟩ := hq.surjective p
  have hp := quotientChart_center (E:=E) q hq a
  have ht := (quotientChart (E:=E) q hq a).map_source hp
  have hlocal : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω
      (f ∘ (quotientChart (E:=E) q hq a).symm)
      (quotientChart q hq a (q a)) := by
    have hA := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) ht.1
    apply ((hlift _).comp _ hA).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z => by
      change f ((quotientChart (E:=E) q hq a).symm z)=lift ((chartAt E a).symm z)
      rw [quotientChart_symm,hsquare])
  have hc := contMDiffAt_of_mem_maximalAtlas (quotientChart_maximal q hq hhol a) hp
  apply (hlocal.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(quotientChart (E:=E) q hq a).open_source.mem_nhds hp] with x hx
  simp only [Function.comp_apply,(quotientChart (E:=E) q hq a).left_inv hx]
end HolomorphicQuotientCoverMaps318
