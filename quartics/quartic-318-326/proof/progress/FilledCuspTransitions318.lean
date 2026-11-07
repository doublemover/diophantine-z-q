module
public import FilledCuspCharts318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 HolomorphicCharts318 FilledCuspCharts318
open scoped Manifold ContDiff
namespace FilledCuspTransitions318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem old_in_new (N:ℕ) (b:Base (image N)) :
    original N b∈(newChart N).source ↔ b∈(ActualCuspPartialChart318.chart N).source := by
  rw [new_source]
  constructor
  · rintro ⟨q,hq⟩
    have hb := ((TwoChartGluing318.left_eq_right_iff (overlap N) b q).mp hq.symm).1
    rwa [overlap_source] at hb
  · intro hb
    have hb':b∈(overlap N).source := by rwa [overlap_source]
    exact ⟨overlap N b,((TwoChartGluing318.left_eq_right_iff _ _ _).mpr ⟨hb',rfl⟩).symm⟩

theorem new_on_old (N:ℕ) (b:Base (image N))
    (hb:b∈(ActualCuspPartialChart318.chart N).source) :
    newChart N (original N b)=ActualCuspPartialChart318.chart N b := by
  have hb':b∈(overlap N).source := by rwa [overlap_source]
  have he:original N b=cuspChart N (overlap N b) :=
    (TwoChartGluing318.left_eq_right_iff _ _ _).mpr ⟨hb',rfl⟩
  rw [he,new_apply]
  exact (ActualCuspPartialChart318.chart N).symm.subtypeRestr_symm_apply disc_nonempty hb'

/-- The actual mixed transition in the glued atlas agrees on exactly its
source with the actual old-chart-to-cusp transition. -/
theorem mixed_transition (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    letI:=complexChartedSpace N hN
    (oldChart N hN b).symm.trans (newChart N) ≈
      (chartAt ℂ b).symm.trans (ActualCuspPartialChart318.chart N) := by
  letI:=complexChartedSpace N hN
  constructor
  · ext z
    change (z∈(chartAt ℂ b).target ∧
      original N ((chartAt ℂ b).symm z)∈(newChart N).source) ↔
        (z∈(chartAt ℂ b).target ∧
          (chartAt ℂ b).symm z∈(ActualCuspPartialChart318.chart N).source)
    rw [old_in_new]
  · intro z hz
    change newChart N (original N ((chartAt ℂ b).symm z))=
      ActualCuspPartialChart318.chart N ((chartAt ℂ b).symm z)
    exact new_on_old N _ ((old_in_new N _).mp hz.2)

/-- Genuine analytic compatibility of the mixed transition follows from the
proved biholomorphic cusp chart, not a supplied transition assumption. -/
theorem mixed_analytic (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    (oldChart N hN b).symm.trans (newChart N)∈contDiffGroupoid ω 𝓘(ℂ) := by
  letI:=complexChartedSpace N hN
  letI:=complex_manifold N hN
  have hc : ActualCuspPartialChart318.chart N∈IsManifold.maximalAtlas 𝓘(ℂ) ω (Base (image N)) :=
    (ActualCuspPartialChart318.chart N).mem_maximalAtlas_of_contMDiffOn
      (BiholomorphicCusp318.chart_biholomorphic N hN).1
      (BiholomorphicCusp318.chart_biholomorphic N hN).2
  exact (contDiffGroupoid ω 𝓘(ℂ)).mem_of_eqOnSource
    (IsManifold.compatible_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas b) hc)
    (mixed_transition N hN b)

end FilledCuspTransitions318
