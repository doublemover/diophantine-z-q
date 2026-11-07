module
public import FilledComplexCurve318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 HolomorphicCharts318 FilledCuspCharts318
open scoped Manifold ContDiff
namespace FilledCuspEmbeddings318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem original_holomorphic (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    letI:=filledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (original N) := by
  letI:=complexChartedSpace N hN
  letI:=complex_manifold N hN
  letI:=filledChartedSpace N hN
  letI:=FilledComplexCurve318.filled_isManifold N hN
  intro b
  have he:oldChart N hN b∈IsManifold.maximalAtlas 𝓘(ℂ) ω (Filled N) :=
    IsManifold.subset_maximalAtlas (Or.inl ⟨b,rfl⟩)
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he (old_center N hN b)).mpr
  refine ⟨(original_isOpenEmbedding N).continuous.continuousAt.continuousWithinAt,?_⟩
  simp only [OpenPartialHomeomorph.extend_coe,modelWithCornersSelf_coe,Function.id_comp]
  have hf : (oldChart N hN b : Filled N→ℂ) ∘ original N = (chartAt ℂ b : Base (image N)→ℂ) :=
    funext (old_apply N hN b)
  rw [hf]
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas b)
    (mem_chart_source ℂ b)).contMDiffWithinAt

theorem disc_holomorphic (N:ℕ) (hN:5≤N) :
    letI:=filledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspChart N) := by
  letI:=filledChartedSpace N hN
  letI:=FilledComplexCurve318.filled_isManifold N hN
  intro q
  have he:newChart N∈IsManifold.maximalAtlas 𝓘(ℂ) ω (Filled N) :=
    IsManifold.subset_maximalAtlas (Or.inr rfl)
  have hq:cuspChart N q∈(newChart N).source := ⟨q,trivial,rfl⟩
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hq).mpr
  refine ⟨(cuspChart_isOpenEmbedding N).continuous.continuousAt.continuousWithinAt,?_⟩
  simp only [OpenPartialHomeomorph.extend_coe,modelWithCornersSelf_coe,Function.id_comp]
  have hf : (newChart N : Filled N→ℂ) ∘ cuspChart N = (Subtype.val : disc→ℂ) :=
    funext (new_apply N)
  rw [hf]
  exact (contMDiff_subtype_val (I:=𝓘(ℂ)) (n:=ω) q).contMDiffWithinAt

end FilledCuspEmbeddings318
