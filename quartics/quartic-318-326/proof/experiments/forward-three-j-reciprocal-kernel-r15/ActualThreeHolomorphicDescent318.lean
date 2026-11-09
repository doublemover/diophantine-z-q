module
public import HolomorphicDescent318
public section
noncomputable section
open Function Filter Topology
namespace ActualThreeHolomorphicDescent318
open ActualThreeExceptionalParameter318 ActualThreeGlobalParameter318
open GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original period parameter is open at every actual upper-half-plane
point, expressed in the original complex source coordinate. -/
theorem period_nhds_le (tau : UpperHalfPlane) :
    𝓝 (periodParameter tau) ≤ Filter.map
      (fun z : ℂ => periodParameter (UpperHalfPlane.ofComplex z)) (𝓝 (tau:ℂ)) := by
  have hs : (tau:ℂ) ∈ UpperHalfPlane.ofComplex.source := by
    simpa only [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using Set.mem_range_self tau
  have he := UpperHalfPlane.ofComplex.map_nhds_eq hs
  rw [UpperHalfPlane.ofComplex_apply] at he
  rw [show (fun z : ℂ => periodParameter (UpperHalfPlane.ofComplex z)) =
    periodParameter ∘ UpperHalfPlane.ofComplex from rfl,←Filter.map_map,he]
  exact periodParameter_isOpenMap.nhds_le tau

/-- Exact holomorphic descent for the original period map, including all its
critical points. The downstairs function has no assumed continuity. -/
theorem analyticAt_iff_period_pullback (F : ℂ → ℂ) (tau : UpperHalfPlane) :
    AnalyticAt ℂ F (periodParameter tau) ↔
      AnalyticAt ℂ (fun z : ℂ => F (periodParameter (UpperHalfPlane.ofComplex z))) (tau:ℂ) := by
  constructor
  · intro hF
    exact hF.comp_of_eq (periodParameter_analyticAt tau) (by simp)
  · intro hp
    simpa only [UpperHalfPlane.ofComplex_apply] using
      HolomorphicDescent318.analyticAt_of_comp_nhds_le
        (periodParameter_analyticAt tau) (by simpa using period_nhds_le tau) hp

/-- Analyticity on the independently specified punctured complex line is
exactly analyticity of the original period pullback everywhere on H. -/
theorem analyticOnNhd_iff_period_pullback (F : ℂ → ℂ) :
    AnalyticOnNhd ℂ F {t : ℂ | t ≠ 0} ↔
      ∀ tau : UpperHalfPlane,
        AnalyticAt ℂ (fun z : ℂ => F (periodParameter (UpperHalfPlane.ofComplex z))) (tau:ℂ) := by
  constructor
  · intro hF tau
    exact (analyticAt_iff_period_pullback F tau).mp (hF _ (periodParameter_ne_zero tau))
  · intro hp t ht
    obtain ⟨tau,he⟩ := ActualThreeParameterProper318.periodParameter_surjective t ht
    rw [←he]
    exact (analyticAt_iff_period_pullback F tau).mpr (hp tau)

end ActualThreeHolomorphicDescent318
