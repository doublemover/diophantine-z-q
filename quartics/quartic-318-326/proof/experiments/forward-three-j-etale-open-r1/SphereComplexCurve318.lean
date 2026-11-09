module
public import SphereCharts318
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public section
noncomputable section
open Function Filter Topology TopologicalSpace
open scoped Manifold ContDiff
namespace SphereComplexCurve318
open SphereCharts318 SphereInversion318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma infinity_apply (z : OnePoint ℂ) : infinityChart z=finiteChart (inversion z) := rfl
lemma infinity_symm_apply (t : ℂ) : infinityChart.symm t=inversion (t : OnePoint ℂ) := rfl

lemma infinity_target : infinityChart.target=Set.univ := by
  simp [infinityChart,finite_target]

lemma finite_infinity_source :
    (finiteChart.symm.trans infinityChart).source={t : ℂ | t ≠ 0} := by
  ext t
  simp only [OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
    finite_target,Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_preimage,finite_symm_apply,
    infinity_source_iff,Set.mem_ofPred_eq]
  by_cases ht : t=0
  · subst t
    rw [inversion_zero]
    simp only [OnePoint.infty_notMem_range_coe,ne_self_iff_false]
  · rw [inversion_coe ht]
    exact iff_of_true (Set.mem_range_self _) ht

lemma infinity_finite_source :
    (infinityChart.symm.trans finiteChart).source={t : ℂ | t ≠ 0} := by
  ext t
  simp only [OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
    infinity_target,Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_preimage,infinity_symm_apply,
    finite_source,Set.mem_ofPred_eq]
  by_cases ht : t=0
  · subst t
    rw [inversion_zero]
    simp only [OnePoint.infty_notMem_range_coe,ne_self_iff_false]
  · rw [inversion_coe ht]
    exact iff_of_true (Set.mem_range_self _) ht

lemma finite_infinity_apply {t : ℂ} (ht : t ≠ 0) :
    (finiteChart.symm.trans infinityChart) t=t⁻¹ := by
  change finiteChart (inversion (t : OnePoint ℂ))=t⁻¹
  rw [inversion_coe ht,finite_apply]

lemma infinity_finite_apply {t : ℂ} (ht : t ≠ 0) :
    (infinityChart.symm.trans finiteChart) t=t⁻¹ := by
  change finiteChart (inversion (t : OnePoint ℂ))=t⁻¹
  rw [inversion_coe ht,finite_apply]

/-- The two independently constructed target sphere charts have the literal
holomorphic reciprocal transition in both directions, on exactly C*. -/
theorem mixed_analytic :
    finiteChart.symm.trans infinityChart ∈ contDiffGroupoid ω 𝓘(ℂ) := by
  have hi : ContDiffOn ℂ ω (fun t : ℂ => t⁻¹) {t : ℂ | t ≠ 0} := by
    intro t ht
    exact (analyticAt_id.inv ht).contDiffAt.contDiffWithinAt
  have hs : finiteChart.target ∩ finiteChart.symm ⁻¹' infinityChart.source = {t : ℂ | t ≠ 0} :=
    finite_infinity_source
  have ht : infinityChart.target ∩ infinityChart.symm ⁻¹' finiteChart.source = {t : ℂ | t ≠ 0} :=
    infinity_finite_source
  constructor
  · simpa only [contDiffPregroupoid,mfld_simps,hs,Function.comp_def] using
      hi.congr (fun t ht => finite_infinity_apply ht)
  · simpa only [contDiffPregroupoid,mfld_simps,ht,Function.comp_def] using
      hi.congr (fun t ht => infinity_finite_apply ht)

/-- The standard one-point compactification carries its independent ordinary
complex-sphere analytic atlas. No modular source enters the construction. -/
theorem sphere_isManifold :
    letI := sphereChartedSpace
    IsManifold 𝓘(ℂ) ω (OnePoint ℂ) := by
  let := sphereChartedSpace
  refine { compatible:=?_ }
  intro e e' he he'
  change e=finiteChart ∨ e=infinityChart at he
  change e'=finiteChart ∨ e'=infinityChart at he'
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · exact symm_trans_mem_contDiffGroupoid finiteChart
  · exact mixed_analytic
  · have h := (contDiffGroupoid ω 𝓘(ℂ)).symm mixed_analytic
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using h
  · exact symm_trans_mem_contDiffGroupoid infinityChart

end SphereComplexCurve318
