module
public import FilledCuspCountable318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 HolomorphicCharts318
namespace FilledCuspCharts318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The old actual quotient charts, transported by the genuine open embedding. -/
@[expose] def oldChart (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    OpenPartialHomeomorph (Filled N) ℂ :=
  letI:=complexChartedSpace N hN
  (chartAt ℂ b).lift_openEmbedding (original_isOpenEmbedding N)

/-- The actual filled-disc coordinate, transported by the genuine gluing embedding. -/
@[expose] def newChart (N:ℕ) : OpenPartialHomeomorph (Filled N) ℂ :=
  (disc.openPartialHomeomorphSubtypeCoe disc_nonempty).lift_openEmbedding
    (cuspChart_isOpenEmbedding N)

theorem old_center (N:ℕ) (hN:5≤N) (b:Base (image N)) : original N b∈(oldChart N hN b).source := by
  letI:=complexChartedSpace N hN
  exact ⟨b,mem_chart_source ℂ b,rfl⟩

theorem new_center (N:ℕ) : cusp N∈(newChart N).source := ⟨zeroPoint,trivial,rfl⟩

theorem new_source (N:ℕ) : (newChart N).source=Set.range (cuspChart N) := by
  simp only [newChart,OpenPartialHomeomorph.lift_openEmbedding_source,
    Opens.openPartialHomeomorphSubtypeCoe_source,Set.image_univ]

theorem new_target (N:ℕ) : (newChart N).target=disc := by
  simp only [newChart,OpenPartialHomeomorph.lift_openEmbedding_target,
    Opens.openPartialHomeomorphSubtypeCoe_target]

theorem new_apply (N:ℕ) (q:disc) : newChart N (cuspChart N q)=(q:ℂ) := by
  exact (disc.openPartialHomeomorphSubtypeCoe disc_nonempty).lift_openEmbedding_apply _

theorem old_apply (N:ℕ) (hN:5≤N) (b c:Base (image N)) :
    letI:=complexChartedSpace N hN
    oldChart N hN b (original N c)=chartAt ℂ b c := by
  letI:=complexChartedSpace N hN
  exact (chartAt ℂ b).lift_openEmbedding_apply _

@[expose] def chosenChart (N:ℕ) (hN:5≤N) (z:Filled N) :
    OpenPartialHomeomorph (Filled N) ℂ := by
  classical
  exact if hz:z=cusp N then newChart N else
    oldChart N hN (((Set.ext_iff.mp (range_original N) z).mpr hz).choose)

theorem chosenChart_source (N:ℕ) (hN:5≤N) (z:Filled N) : z∈(chosenChart N hN z).source := by
  classical
  unfold chosenChart
  split_ifs with hz
  · simpa only [hz] using new_center N
  · have h := ((Set.ext_iff.mp (range_original N) z).mpr hz).choose_spec
    exact Set.mem_of_eq_of_mem h.symm (old_center N hN _)

/-- A genuine complex-coordinate topological atlas on the actual Hausdorff,
second-countable one-cusp attachment. Transition analyticity is separate. -/
@[expose,instance_reducible] def filledChartedSpace (N:ℕ) (hN:5≤N) :
    ChartedSpace ℂ (Filled N) where
  atlas := Set.range (oldChart N hN) ∪ {newChart N}
  chartAt := chosenChart N hN
  mem_chart_source := chosenChart_source N hN
  chart_mem_atlas z := by
    classical
    unfold chosenChart
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl ⟨_,rfl⟩

end FilledCuspCharts318
