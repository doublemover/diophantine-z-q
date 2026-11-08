module
public import RotatedBiholomorphic318
public import AllCuspInfinity318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 HolomorphicCharts318
namespace AllCuspCharts318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

instance disc_nonempty (N:ℕ) (hN:5≤N) (c:End N) : Nonempty (disc N hN c):=⟨zeroPoint N hN c⟩
@[expose] def discOpen (N:ℕ) (hN:5≤N) (c:End N) : Opens ℂ:=⟨disc N hN c,disc_open N hN c⟩

@[expose] def oldChart (N:ℕ) (hN:5≤N) (b:Base (image N)) : OpenPartialHomeomorph (Filled N hN) ℂ :=
  letI:=complexChartedSpace N hN
  (chartAt ℂ b).lift_openEmbedding (original_openEmbedding N hN)

@[expose] def newChart (N:ℕ) (hN:5≤N) (c:End N) : OpenPartialHomeomorph (Filled N hN) ℂ :=
  ((discOpen N hN c).openPartialHomeomorphSubtypeCoe (disc_nonempty N hN c)).lift_openEmbedding
    (cuspChart_openEmbedding N hN c)

theorem old_center (N:ℕ) (hN:5≤N) (b:Base (image N)) : original N hN b∈(oldChart N hN b).source := by
  letI:=complexChartedSpace N hN
  exact ⟨b,mem_chart_source ℂ b,rfl⟩

theorem new_center (N:ℕ) (hN:5≤N) (c:End N) : cusp N hN c∈(newChart N hN c).source :=
  ⟨zeroPoint N hN c,trivial,rfl⟩

theorem new_source (N:ℕ) (hN:5≤N) (c:End N) : (newChart N hN c).source=Set.range (cuspChart N hN c) := by
  simp only [newChart,OpenPartialHomeomorph.lift_openEmbedding_source,
    Opens.openPartialHomeomorphSubtypeCoe_source,Set.image_univ]
  rfl

theorem new_target (N:ℕ) (hN:5≤N) (c:End N) : (newChart N hN c).target=disc N hN c := by
  simp only [newChart,OpenPartialHomeomorph.lift_openEmbedding_target,
    Opens.openPartialHomeomorphSubtypeCoe_target,discOpen]
  rfl

theorem new_apply (N:ℕ) (hN:5≤N) (c:End N) (q:disc N hN c) :
    newChart N hN c (cuspChart N hN c q)=q.val :=
  ((discOpen N hN c).openPartialHomeomorphSubtypeCoe (disc_nonempty N hN c)).lift_openEmbedding_apply _

theorem old_apply (N:ℕ) (hN:5≤N) (b d:Base (image N)) :
    letI:=complexChartedSpace N hN
    oldChart N hN b (original N hN d)=chartAt ℂ b d := by
  letI:=complexChartedSpace N hN
  exact (chartAt ℂ b).lift_openEmbedding_apply _

@[expose] def chosenChart (N:ℕ) (hN:5≤N) (z:Filled N hN) : OpenPartialHomeomorph (Filled N hN) ℂ := by
  classical
  exact if hz:z∈Set.range (cusp N hN) then newChart N hN hz.choose else
    oldChart N hN (((Set.ext_iff.mp (range_original N hN) z).mpr hz).choose)

theorem chosenChart_source (N:ℕ) (hN:5≤N) (z:Filled N hN) : z∈(chosenChart N hN z).source := by
  classical
  unfold chosenChart
  split_ifs with hz
  · exact Set.mem_of_eq_of_mem hz.choose_spec.symm (new_center N hN hz.choose)
  · have h:=((Set.ext_iff.mp (range_original N hN) z).mpr hz).choose_spec
    exact Set.mem_of_eq_of_mem h.symm (old_center N hN _)

/-- Actual complex-coordinate atlas on the genuine all-cusp topological
compactification, including every cusp disc and the original complex atlas. -/
@[expose,instance_reducible] def filledChartedSpace (N:ℕ) (hN:5≤N) : ChartedSpace ℂ (Filled N hN) where
  atlas:=Set.range (oldChart N hN) ∪ Set.range (newChart N hN)
  chartAt:=chosenChart N hN
  mem_chart_source:=chosenChart_source N hN
  chart_mem_atlas z:=by
    classical
    unfold chosenChart
    split_ifs
    · exact Or.inr ⟨_,rfl⟩
    · exact Or.inl ⟨_,rfl⟩

end AllCuspCharts318
