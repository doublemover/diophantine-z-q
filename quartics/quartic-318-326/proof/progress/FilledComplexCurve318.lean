module
public import FilledCuspTransitions318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 HolomorphicCharts318 FilledCuspCharts318
open scoped Manifold ContDiff
namespace FilledComplexCurve318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual one-cusp attachment is a genuine complex analytic manifold:
all old, new and mixed chart transitions are proved analytic. -/
theorem filled_isManifold (N:ℕ) (hN:5≤N) :
    letI:=filledChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (Filled N) := by
  letI:=filledChartedSpace N hN
  refine { compatible := ?_ }
  intro e e' he he'
  rcases he with ⟨b,rfl⟩ | rfl
  · rcases he' with ⟨c,rfl⟩ | rfl
    · letI:=complexChartedSpace N hN
      letI:=complex_manifold N hN
      change ((chartAt ℂ b).lift_openEmbedding (original_isOpenEmbedding N)).symm.trans
        ((chartAt ℂ c).lift_openEmbedding (original_isOpenEmbedding N))∈contDiffGroupoid ω 𝓘(ℂ)
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact IsManifold.compatible_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas b) (IsManifold.chart_mem_maximalAtlas c)
    · exact FilledCuspTransitions318.mixed_analytic N hN b
  · rcases he' with ⟨c,rfl⟩ | rfl
    · have h := (contDiffGroupoid ω 𝓘(ℂ)).symm (FilledCuspTransitions318.mixed_analytic N hN c)
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using h
    · exact symm_trans_mem_contDiffGroupoid (newChart N)

/-- The analytic curve is Hausdorff and second countable as well as charted;
these properties refer to the genuine gluing topology. -/
theorem filled_complex_curve (N:ℕ) (hN:5≤N) :
    letI:=filledChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (Filled N) ∧ T2Space (Filled N) ∧ SecondCountableTopology (Filled N) := by
  letI:=filledChartedSpace N hN
  exact ⟨filled_isManifold N hN,FilledCuspHausdorff318.filled_t2 N hN,
    FilledCuspCountable318.filled_secondCountable N⟩

end FilledComplexCurve318
