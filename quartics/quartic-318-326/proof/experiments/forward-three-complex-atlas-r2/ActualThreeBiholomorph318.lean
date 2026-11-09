module
public import ActualThreeCanonicalAnalytic318
public import Mathlib.Geometry.Manifold.Diffeomorph
public section
noncomputable section
open Function Filter Topology
open scoped Manifold ContDiff
namespace ActualThreeBiholomorph318
open SphereCharts318 SphereComplexCurve318 ActualThreeComplexAtlas318
open ActualThreeFilledParameter318 ActualThreeCuspFilling318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma chart_cancel_analytic (w : OnePoint ℂ) :
    AnalyticAt ℂ (fun t => chosenChart w ((chosenChart w).symm t)) (chosenChart w w) := by
  let := sphereChartedSpace
  have hc : chosenChart w w ∈ (chosenChart w).target :=
    (chosenChart w).map_source (mem_chart_source ℂ w)
  apply analyticAt_id.congr
  filter_upwards [(chosenChart w).open_target.mem_nhds hc] with t ht
  exact ((chosenChart w).right_inv ht).symm

/-- The exact original compact comparison is holomorphic for the actual source
structure identified with orbit and q-disc holomorphy in the previous module. -/
theorem compact_contMDiff :
    letI := filledChartedSpace
    letI := sphereChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω compactHomeomorph := by
  let := filledChartedSpace
  let := sphereChartedSpace
  intro z
  apply contMDiffAt_iff.mpr
  refine ⟨compactHomeomorph.continuous.continuousAt,?_⟩
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,contDiffWithinAt_univ,
    Function.comp_id,Function.id_comp]
  change ContDiffAt ℂ ω
    (fun t => chosenChart (compactHomeomorph z)
      (compactHomeomorph ((sourceChart (chosenChart (compactHomeomorph z))).symm t)))
    (sourceChart (chosenChart (compactHomeomorph z)) z)
  rw [sourceChart_apply]
  simpa only [sourceChart,OpenPartialHomeomorph.lift_openEmbedding_symm,Function.comp_apply,
    Homeomorph.apply_symm_apply] using (chart_cancel_analytic (compactHomeomorph z)).contDiffAt

/-- The inverse of the exact original compact comparison is holomorphic too. -/
theorem compact_symm_contMDiff :
    letI := filledChartedSpace
    letI := sphereChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω compactHomeomorph.symm := by
  let := filledChartedSpace
  let := sphereChartedSpace
  intro w
  apply contMDiffAt_iff.mpr
  refine ⟨compactHomeomorph.symm.continuous.continuousAt,?_⟩
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,contDiffWithinAt_univ,
    Function.comp_id,Function.id_comp]
  change ContDiffAt ℂ ω
    (fun t => sourceChart (chosenChart (compactHomeomorph (compactHomeomorph.symm w)))
      (compactHomeomorph.symm ((chosenChart w).symm t))) (chosenChart w w)
  simpa only [sourceChart_apply,Homeomorph.apply_symm_apply] using
    (chart_cancel_analytic w).contDiffAt

/-- The original compact level-three comparison, now as a genuine complex
analytic equivalence with the independently charted standard complex sphere. -/
@[expose] def compactBiholomorph :
    letI := filledChartedSpace
    letI := sphereChartedSpace
    Filled ≃ₘ^ω⟮𝓘(ℂ),𝓘(ℂ)⟯ OnePoint ℂ :=
  { compactHomeomorph.toEquiv with
    contMDiff_toFun := compact_contMDiff
    contMDiff_invFun := compact_symm_contMDiff }

lemma compactBiholomorph_apply (z : Filled) :
    letI := filledChartedSpace
    letI := sphereChartedSpace
    compactBiholomorph z=compactHomeomorph z := rfl

lemma compactBiholomorph_symm_apply (z : OnePoint ℂ) :
    letI := filledChartedSpace
    letI := sphereChartedSpace
    compactBiholomorph.symm z=compactHomeomorph.symm z := rfl

end ActualThreeBiholomorph318
