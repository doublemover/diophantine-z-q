module
public import HolomorphicCharts318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318 HolomorphicCharts318
open Filter Topology
open scoped Manifold ContDiff
namespace HolomorphicProjection318
set_option maxHeartbeats 0

/-- The actual orbit projection is holomorphic for the constructed complex manifold,
not just a topological covering map. -/
theorem quotient_holomorphic (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (quotientMap N) := by
  letI:=complexChartedSpace N hN
  intro z
  apply contMDiffAt_iff_target.mpr
  refine ⟨(quotient_covering N hN).isCoveringMap.continuous.continuousAt,?_⟩
  rw [UpperHalfPlane.contMDiffAt_iff]
  let a:UpperHalfPlane := (quotient_surjective N (quotientMap N z)).choose
  have ha:quotientMap N a=quotientMap N z := (quotient_surjective N _).choose_spec
  have hz:quotientMap N z∈((quotient_localHomeomorph N hN).localInverseAt a).source := by
    rw [←ha]
    exact (quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source
  have han:=InverseCoordinate318.analytic_localInverseAt N hN a z hz
  simp only [extChartAt_coe,modelWithCornersSelf_coe,Function.id_comp]
  change ContDiffAt ℂ ω (fun w:ℂ=>localChart N hN a (quotientMap N (ofComplex w))) (z:ℂ)
  simpa only [localChart_apply] using han.contDiffAt
end HolomorphicProjection318
