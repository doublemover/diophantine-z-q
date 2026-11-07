module
public import FilledJ318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 FilledCuspCharts318 FilledJ318
open HolomorphicCharts318 QuotientJ318
open scoped Manifold ContDiff
namespace FilledJHolomorphic318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem old_coordinate (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    letI:=complexChartedSpace N hN
    filledJ N ∘ (oldChart N hN b).symm = jMap N ∘ (chartAt ℂ b).symm := by
  letI:=complexChartedSpace N hN
  funext q
  change filledJ N (original N ((chartAt ℂ b).symm q)) = _
  exact filledJ_original N _

/-- Holomorphy on the actual old open subset of the filled complex curve. -/
theorem old_holomorphic (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    letI:=filledChartedSpace N hN
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (filledJ N) (original N b) := by
  letI:=complexChartedSpace N hN
  letI:=complex_manifold N hN
  letI:=filledChartedSpace N hN
  letI:=FilledComplexCurve318.filled_isManifold N hN
  have he:oldChart N hN b∈IsManifold.maximalAtlas 𝓘(ℂ) ω (Filled N) :=
    IsManifold.subset_maximalAtlas (Or.inl ⟨b,rfl⟩)
  apply (contMDiffWithinAt_iff_source_of_mem_maximalAtlas he (old_center N hN b)).mpr
  have hb:ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (jMap N) b :=
    HolomorphicQuotientJ318.jMap_holomorphic N hN b
  have hc := (contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas b) (mem_chart_source ℂ b)).mp hb
  simpa only [OpenPartialHomeomorph.extend_coe,OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,old_coordinate,old_apply,Set.preimage_univ] using hc

theorem holomorphic_off_cusp (N:ℕ) (hN:5≤N) (z:Filled N) (hz:z≠cusp N) :
    letI:=filledChartedSpace N hN
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (filledJ N) z := by
  obtain ⟨b,rfl⟩ := (Set.ext_iff.mp (range_original N) z).mpr hz
  exact old_holomorphic N hN b

end FilledJHolomorphic318
