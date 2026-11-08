module
public import AllCuspComplexCurve318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 AllCuspFilling318 AllCuspOverlap318 FiniteCuspEnds318 HolomorphicCharts318 AllCuspCharts318
open scoped Manifold ContDiff
namespace AllCuspEmbeddings318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem original_holomorphic (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    letI:=filledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (original N hN) := by
  letI:=complexChartedSpace N hN
  letI:=complex_manifold N hN
  letI:=filledChartedSpace N hN
  letI:=AllCuspComplexCurve318.filled_isManifold N hN
  intro b
  have he:oldChart N hN b∈IsManifold.maximalAtlas 𝓘(ℂ) ω (Filled N hN) :=
    IsManifold.subset_maximalAtlas (Or.inl ⟨b,rfl⟩)
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he (old_center N hN b)).mpr
  refine ⟨(original_openEmbedding N hN).continuous.continuousAt.continuousWithinAt,?_⟩
  simp only [OpenPartialHomeomorph.extend_coe,modelWithCornersSelf_coe,Function.id_comp]
  have hf : (oldChart N hN b : Filled N hN→ℂ) ∘ original N hN = (chartAt ℂ b : Base (image N)→ℂ) :=
    funext (old_apply N hN b)
  rw [hf]
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas b)
    (mem_chart_source ℂ b)).contMDiffWithinAt

theorem disc_holomorphic (N:ℕ) (hN:5≤N) (c:End N) :
    letI:=filledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun q:discOpen N hN c=>cuspChart N hN c q) := by
  letI:=filledChartedSpace N hN
  letI:=AllCuspComplexCurve318.filled_isManifold N hN
  intro q
  have he:newChart N hN c∈IsManifold.maximalAtlas 𝓘(ℂ) ω (Filled N hN) :=
    IsManifold.subset_maximalAtlas (Or.inr ⟨c,rfl⟩)
  have hq:cuspChart N hN c q∈(newChart N hN c).source := ⟨q,trivial,rfl⟩
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hq).mpr
  refine ⟨(cuspChart_openEmbedding N hN c).continuous.continuousAt.continuousWithinAt,?_⟩
  simp only [OpenPartialHomeomorph.extend_coe,modelWithCornersSelf_coe,Function.id_comp]
  have hf : (fun q:discOpen N hN c=>newChart N hN c (cuspChart N hN c q)) = (Subtype.val : discOpen N hN c→ℂ) :=
    funext (new_apply N hN c)
  change ContMDiffWithinAt 𝓘(ℂ) 𝓘(ℂ) ω
    (fun q:discOpen N hN c=>newChart N hN c (cuspChart N hN c q)) Set.univ q
  rw [hf]
  exact (contMDiff_subtype_val (I:=𝓘(ℂ)) (n:=ω) (U:=discOpen N hN c) q).contMDiffWithinAt

end AllCuspEmbeddings318
