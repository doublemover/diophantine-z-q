module
public import HolomorphicQuotientCoverMaps318
public section
noncomputable section
namespace HolomorphicQuotientInverse318
open HolomorphicQuotientCoverCharts318 HolomorphicQuotientCoverMaps318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1200000
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [TopologicalSpace Q] [Group G] [MulAction G M] [ContinuousConstSMul G M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ω M]
variable (q : M → Q) (hq : IsQuotientCoveringMap q G)
  (hhol : ∀ g : G, ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) ω (fun x : M => g • x))
local instance : ChartedSpace E Q := quotientCharts q hq
local instance : IsManifold 𝓘(ℂ,E) ω Q := quotient_manifold q hq hhol

include hhol in
/-- Actual inverse covering branches, now holomorphic into the ORIGINAL
covering manifold on their full original-chart source neighborhoods. -/
theorem inverse_holomorphicAt (a : M) (p : Q)
    (hp : p∈(quotientChart (E:=E) q hq a).source) :
    ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,E) ω (inverseChart q hq a) p := by
  have ht : quotientChart (E:=E) q hq a p∈(chartAt E a).target :=
    (chartAt E a).map_source hp.2
  have hi := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) ht
  have hc := contMDiffAt_of_mem_maximalAtlas (quotientChart_maximal q hq hhol a) hp
  apply (hi.comp p hc).congr_of_eventuallyEq
  filter_upwards [(quotientChart (E:=E) q hq a).open_source.mem_nhds hp] with z hz
  exact ((chartAt E a).left_inv hz.2).symm

theorem inverse_projection (a : M) (p : Q) (hp : p∈(inverseChart q hq a).source) :
    q (inverseChart q hq a p)=p := by
  have h := (inverseChart q hq a).left_inv hp
  rwa [inverseChart_symm] at h
end HolomorphicQuotientInverse318
