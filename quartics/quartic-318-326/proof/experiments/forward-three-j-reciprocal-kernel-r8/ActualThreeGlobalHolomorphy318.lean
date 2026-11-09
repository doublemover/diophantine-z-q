module
public import ActualThreeBiholomorph318
public section
noncomputable section
open Function Filter Topology
open scoped Manifold ContDiff
namespace ActualThreeGlobalHolomorphy318
open GammaOneFiber318 PeterssonQuotient318 FiniteCuspEnds318
open ActualThreeCuspFilling318 ActualThreeQuotientHolomorphic318
open ActualThreeFilledHolomorphic318 ActualThreeFilledParameter318
open ActualThreeComplexAtlas318 ActualThreeCanonicalAnalytic318
open ActualThreeBiholomorph318 SphereCharts318 SphereComplexCurve318

/-- Global holomorphy defined directly on the original quotient and every
actual cusp disc, without referring to the transported atlas or target map. -/
@[expose] def SourceHolomorphic (u : Filled → ℂ) : Prop :=
  (∀ b : Base (image 3), QuotientHolomorphicAt (u ∘ original) b) ∧
    ∀ c : End 3, AnalyticAt ℂ (fun q => u (sourceDisc c q)) 0

/-- The bundled analytic structure has exactly the independently defined
global source functions. Exhaustion includes all original elliptic points
and every actual cusp, not just a dense open subset. -/
theorem contMDiff_iff_source (u : Filled → ℂ) :
    letI := filledChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω u ↔ SourceHolomorphic u := by
  letI := filledChartedSpace
  constructor
  · intro h
    exact ⟨fun b => (original_canonical_iff u b).mp (h (original b)),
      fun c => (cusp_canonical_iff u c).mp (h (cusp c))⟩
  · rintro ⟨ho,hc⟩ z
    rcases every_point_has_source_germ z with ⟨b,rfl⟩ | ⟨c,rfl⟩
    · exact (original_canonical_iff u b).mpr (ho b)
    · exact (cusp_canonical_iff u c).mpr (hc c)

/-- Expressing a function through the original compact parameter preserves
and reflects global analytic regularity for the two exact bundled atlases. -/
theorem targetExpression_contMDiff_iff (u : Filled → ℂ) :
    letI := filledChartedSpace
    letI := sphereChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (targetExpression u) ↔
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω u := by
  letI := filledChartedSpace
  letI := sphereChartedSpace
  letI := filled_isManifold
  letI := sphere_isManifold
  constructor
  · intro h
    have hc := h.comp compact_contMDiff
    have he : targetExpression u ∘ compactHomeomorph = u := by
      funext z
      exact congrArg u (compactHomeomorph.symm_apply_apply z)
    rw [he] at hc
    exact hc
  · intro h
    exact h.comp compact_symm_contMDiff

/-- Full source-to-sphere holomorphic function comparison. The left side uses
the independent sphere atlas; the right side uses only the original orbit
projection and genuine selected q discs. -/
theorem targetExpression_contMDiff_iff_source (u : Filled → ℂ) :
    letI := filledChartedSpace
    letI := sphereChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (targetExpression u) ↔ SourceHolomorphic u := by
  letI := filledChartedSpace
  letI := sphereChartedSpace
  exact (targetExpression_contMDiff_iff u).trans (contMDiff_iff_source u)

end ActualThreeGlobalHolomorphy318
