module
public import AllCuspTransitions318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 HolomorphicCharts318 AllCuspCharts318
open scoped Manifold ContDiff
namespace AllCuspComplexCurve318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- All actual chart transitions of the simultaneous all-cusp attachment are
holomorphic, including every mixed old/cusp pair. -/
theorem filled_isManifold (N:ℕ) (hN:5≤N) :
    letI:=filledChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (Filled N hN) := by
  letI:=filledChartedSpace N hN
  refine { compatible:=?_ }
  intro e e' he he'
  rcases he with ⟨b,rfl⟩|⟨c,rfl⟩
  · rcases he' with ⟨b',rfl⟩|⟨d,rfl⟩
    · letI:=complexChartedSpace N hN
      letI:=complex_manifold N hN
      change ((chartAt ℂ b).lift_openEmbedding (original_openEmbedding N hN)).symm.trans
        ((chartAt ℂ b').lift_openEmbedding (original_openEmbedding N hN))∈contDiffGroupoid ω 𝓘(ℂ)
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact IsManifold.compatible_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas b) (IsManifold.chart_mem_maximalAtlas b')
    · exact AllCuspTransitions318.mixed_analytic N hN d b
  · rcases he' with ⟨b,rfl⟩|⟨d,rfl⟩
    · have h:=(contDiffGroupoid ω 𝓘(ℂ)).symm (AllCuspTransitions318.mixed_analytic N hN c b)
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using h
    · by_cases hcd:c=d
      · subst d;exact symm_trans_mem_contDiffGroupoid (newChart N hN c)
      · apply (contDiffGroupoid ω 𝓘(ℂ)).locality'
        intro q hq
        rw [AllCuspTransitions318.distinct_transition_source_empty N hN c d hcd] at hq
        exact False.elim hq

/-- The genuine all-cusp compactification is a compact complex analytic curve,
with its actual Hausdorff and second-countable gluing topology. -/
theorem actual_compact_complex_curve (N:ℕ) (hN:5≤N) :
    letI:=filledChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (Filled N hN) ∧ CompactSpace (Filled N hN) ∧
      T2Space (Filled N hN) ∧ SecondCountableTopology (Filled N hN) := by
  letI:=filledChartedSpace N hN
  exact ⟨filled_isManifold N hN,AllCuspCompact318.filled_compactSpace N hN,
    AllCuspHausdorff318.filled_t2 N hN,filled_secondCountable N hN⟩

end AllCuspComplexCurve318
