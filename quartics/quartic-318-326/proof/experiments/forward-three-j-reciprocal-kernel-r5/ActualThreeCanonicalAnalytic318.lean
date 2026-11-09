module
public import ActualThreeComplexAtlas318
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public section
noncomputable section
open Function Filter Topology
open scoped Manifold ContDiff
namespace ActualThreeCanonicalAnalytic318
open SphereCharts318 SphereComplexCurve318 SphereInversion318 ActualThreeComplexAtlas318
open ActualThreeFilledParameter318 ActualThreeFilledHolomorphic318 ActualThreeCuspFilling318
open ActualThreeQuotientHolomorphic318 ActualThreeExceptionalParameter318
open ActualThreeCuspExhaustion318 GammaOneFiber318 PeterssonQuotient318 FiniteCuspEnds318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual bundled analytic manifold's scalar germ criterion, in the exact
chosen independent sphere coordinate and the exact original compact map. -/
theorem contMDiffAt_iff_coordinate (u : Filled → ℂ) (z : Filled) :
    letI := filledChartedSpace
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u z ↔
      AnalyticAt ℂ (fun t => targetExpression u ((chosenChart (compactHomeomorph z)).symm t))
        (chosenChart (compactHomeomorph z) (compactHomeomorph z))  := by
  let := filledChartedSpace
  rw [contMDiffAt_iff_source]
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt,Function.comp_id,Function.id_comp]
  change ContDiffAt ℂ ω (u ∘ (sourceChart (chosenChart (compactHomeomorph z))).symm)
    (sourceChart (chosenChart (compactHomeomorph z)) z) ↔ _
  rw [sourceChart_apply]
  change ContDiffAt ℂ ω (fun t => targetExpression u
    ((chosenChart (compactHomeomorph z)).symm t)) _ ↔ _
  exact ⟨fun h => h.analyticAt,fun h => h.contDiffAt⟩

/-- The new bundled analytic structure is identified with the independently
defined original orbit-pullback holomorphy, including elliptic points. -/
theorem original_canonical_iff (u : Filled → ℂ) (b : Base (image 3)) :
    letI := filledChartedSpace
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u (original b) ↔ QuotientHolomorphicAt (u ∘ original) b  := by
  let := filledChartedSpace
  rw [contMDiffAt_iff_coordinate,compactHomeomorph_original]
  simp only [chosenChart,OnePoint.coe_ne_infty,ite_false,finite_symm_apply,finite_apply]
  exact (original_holomorphic_iff u b).symm

/-- The new bundled analytic structure is identified with the actual original
selected q-disc germ at every added cusp. This is the explicit canonical-source
comparison which transport of a target atlas alone would not establish. -/
theorem cusp_canonical_iff (u : Filled → ℂ) (c : End 3) :
    letI := filledChartedSpace
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u (cusp c) ↔
      AnalyticAt ℂ (fun q => u (sourceDisc c q)) 0  := by
  let := filledChartedSpace
  rw [contMDiffAt_iff_coordinate]
  rcases end_exhaustion c with rfl | rfl
  · rw [show compactHomeomorph (cusp infinityEnd)=(OnePoint.infty : OnePoint ℂ) from
      compactHomeomorph_infinity]
    simp only [chosenChart,ite_true,infinity_apply,inversion_infty,finite_apply,
      infinity_symm_apply]
    simpa only [inverseSphereChart,ite_true,inversion,OnePoint.elim_some] using
      (cusp_holomorphic_iff u infinityEnd).symm
  · rw [show compactHomeomorph (cusp zeroEnd)=(0:ℂ) from compactHomeomorph_zero]
    simp only [chosenChart,OnePoint.coe_ne_infty,ite_false,finite_symm_apply,finite_apply]
    simpa only [inverseSphereChart,ends_distinct.symm,ite_false] using
      (cusp_holomorphic_iff u zeroEnd).symm

end ActualThreeCanonicalAnalytic318
