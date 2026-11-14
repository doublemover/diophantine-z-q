module
public import HolomorphicQuotientCoverCharts318
public section
noncomputable section
namespace CoveringLiftLocalAction318
open Set Filter
open scoped Topology
variable {M Q G X : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace X] [Group G] [MulAction G M] [ContinuousConstSMul G M]

/-- Two genuine continuous lifts of the same map through a quotient
cover differ near their common base point by ONE fixed original group element. -/
theorem exists_action (q : M → Q) (hq : IsQuotientCoveringMap q G)
    (f g : X → M) (x : X) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (he : (fun y => q (f y)) =ᶠ[𝓝 x] (fun y => q (g y))) :
    ∃ u : G, (fun y => g y) =ᶠ[𝓝 x] (fun y => u • f y) := by
  obtain ⟨u,hu⟩ := hq.apply_eq_iff_mem_orbit.mp he.self_of_nhds.symm
  change u • f x = g x at hu
  let e := hq.isLocalHomeomorph.localInverseAt (g x)
  have hcenter : g x ∈ e.target :=
    hq.isLocalHomeomorph.self_mem_localInverseAt_target
  have huf : ContinuousAt (fun y => u • f y) x :=
    (continuous_const_smul u).continuousAt.comp hf
  have hnearF : ∀ᶠ y in 𝓝 x,u • f y ∈ e.target :=
    huf.eventually (by rw [hu]; exact e.open_target.mem_nhds hcenter)
  have hnearG := hg.eventually (e.open_target.mem_nhds hcenter)
  have hqU (y : M) : q (u • y) = q y := hq.apply_eq_iff_mem_orbit.mpr ⟨u,rfl⟩
  refine ⟨u,?_⟩
  filter_upwards [hnearF,hnearG,he] with y hfy hgy hey
  apply hq.isLocalHomeomorph.injOn_localInverseAt_target hgy hfy
  rw [hqU,hey]
end CoveringLiftLocalAction318
