module
public import ProjectiveLineComplexAtlas318
public import ActualThreeBiholomorph318
public section
noncomputable section
open Function Filter Topology
open scoped Manifold ContDiff
namespace ProjectiveLineBiholomorph318
open ProjectiveLineComplexTopology318 ProjectiveLineComplexAtlas318
open SphereCharts318 SphereComplexCurve318 ActualThreeBiholomorph318

local instance : TopologicalSpace ComplexPoints := complexPointTopology

/-- The exact sphere-to-scheme-point homeomorphism is analytic for the charts
whose inverses are the two actual algebraic evaluation maps. -/
theorem point_contMDiff :
    letI := sphereChartedSpace
    letI := pointChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω pointHomeomorph := by
  letI := sphereChartedSpace
  letI := pointChartedSpace
  intro w
  apply contMDiffAt_iff.mpr
  refine ⟨pointHomeomorph.continuous.continuousAt,?_⟩
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,contDiffWithinAt_univ,
    Function.comp_id,Function.id_comp]
  change ContDiffAt ℂ ω
    (fun t => pointChart (chosenChart (pointHomeomorph.symm (pointHomeomorph w)))
      (pointHomeomorph ((chosenChart w).symm t))) (chosenChart w w)
  simpa only [pointChart_apply,Homeomorph.symm_apply_apply] using
    (chart_cancel_analytic w).contDiffAt

/-- The inverse comparison is analytic in the same actual evaluation atlas. -/
theorem point_symm_contMDiff :
    letI := sphereChartedSpace
    letI := pointChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω pointHomeomorph.symm := by
  letI := sphereChartedSpace
  letI := pointChartedSpace
  intro p
  apply contMDiffAt_iff.mpr
  refine ⟨pointHomeomorph.symm.continuous.continuousAt,?_⟩
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,contDiffWithinAt_univ,
    Function.comp_id,Function.id_comp]
  change ContDiffAt ℂ ω
    (fun t => chosenChart (pointHomeomorph.symm p)
      (pointHomeomorph.symm ((pointChart (chosenChart (pointHomeomorph.symm p))).symm t)))
    (pointChart (chosenChart (pointHomeomorph.symm p)) p)
  rw [pointChart_apply]
  simpa only [pointChart_symm_apply,Homeomorph.symm_apply_apply] using
    (chart_cancel_analytic (pointHomeomorph.symm p)).contDiffAt

/-- Biholomorphic realization of the explicit arithmetic projective line's
actual complex-valued points with their proved algebraic coordinate atlas.
This is not an assertion of a general scheme analytification functor. -/
@[expose] def pointBiholomorph :
    letI := sphereChartedSpace
    letI := pointChartedSpace
    OnePoint ℂ ≃ₘ^ω⟮𝓘(ℂ),𝓘(ℂ)⟯ ComplexPoints := by
  letI := sphereChartedSpace
  letI := pointChartedSpace
  exact { pointHomeomorph.toEquiv with
    contMDiff_toFun := point_contMDiff
    contMDiff_invFun := point_symm_contMDiff }

lemma pointBiholomorph_apply (w : OnePoint ℂ) :
    letI := sphereChartedSpace
    letI := pointChartedSpace
    pointBiholomorph w = pointHomeomorph w := rfl

lemma pointBiholomorph_symm_apply (p : ComplexPoints) :
    letI := sphereChartedSpace
    letI := pointChartedSpace
    pointBiholomorph.symm p = pointHomeomorph.symm p := rfl

end ProjectiveLineBiholomorph318
