module
public import ProjectiveLineComplexTopology318
public import SphereComplexCurve318
public section
noncomputable section
open Function Filter Topology TopologicalSpace
open scoped Manifold ContDiff
namespace ProjectiveLineComplexAtlas318
open ProjectiveLineFieldPoints318 ProjectiveLineComplexTopology318
open SphereCharts318 SphereComplexCurve318

local instance : TopologicalSpace ComplexPoints := complexPointTopology

/-- Charts on the actual scheme-valued points, in their algebraic-evaluation
topology. Their inverse maps are identified below with the original algebraic
polynomial evaluation maps, not only with a transported abstract coordinate. -/
@[expose] def pointChart (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    OpenPartialHomeomorph ComplexPoints ℂ :=
  e.lift_openEmbedding pointHomeomorph.isOpenEmbedding

lemma pointChart_apply (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (p : ComplexPoints) : pointChart e p = e (pointHomeomorph.symm p) := by
  calc
    pointChart e p = pointChart e (pointHomeomorph (pointHomeomorph.symm p)) :=
      congrArg (pointChart e) (pointHomeomorph.apply_symm_apply p).symm
    _ = e (pointHomeomorph.symm p) := e.lift_openEmbedding_apply _

lemma pointChart_symm_apply (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) (t : ℂ) :
    (pointChart e).symm t = pointHomeomorph (e.symm t) := rfl

/-- The finite inverse chart is literally the original scheme morphism
obtained by evaluating the affine coordinate at t. -/
lemma finite_pointChart_symm (t : ℂ) :
    (pointChart finiteChart).symm t = chartPoint (R:=ℚ) 1 t := rfl

/-- The other inverse chart is the original reciprocal algebraic chart,
including its actual origin at infinity. -/
lemma infinity_pointChart_symm (t : ℂ) :
    (pointChart infinityChart).symm t = chartPoint (R:=ℚ) 0 t := by
  exact pointMap_inversion t

lemma pointChart_target (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    (pointChart e).target = e.target := rfl

lemma point_transition (e e' : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    (pointChart e).symm.trans (pointChart e') = e.symm.trans e' :=
  OpenPartialHomeomorph.lift_openEmbedding_trans e e' pointHomeomorph.isOpenEmbedding

@[expose,instance_reducible] def pointChartedSpace : ChartedSpace ℂ ComplexPoints where
  atlas := pointChart '' {finiteChart,infinityChart}
  chartAt p := pointChart (chosenChart (pointHomeomorph.symm p))
  mem_chart_source p := by
    letI := sphereChartedSpace
    exact ⟨pointHomeomorph.symm p,mem_chart_source ℂ (pointHomeomorph.symm p),
      pointHomeomorph.apply_symm_apply p⟩
  chart_mem_atlas p := by
    letI := sphereChartedSpace
    exact ⟨chosenChart (pointHomeomorph.symm p),
      chart_mem_atlas ℂ (pointHomeomorph.symm p),rfl⟩

/-- The actual algebraic-evaluation charts define a complex analytic manifold
on the unchanged scheme-valued point set and its independently defined topology. -/
theorem point_isManifold :
    letI := pointChartedSpace
    IsManifold 𝓘(ℂ) ω ComplexPoints := by
  letI := pointChartedSpace
  letI := sphereChartedSpace
  letI := sphere_isManifold
  refine { compatible := ?_ }
  intro a a' ha ha'
  obtain ⟨e,he,rfl⟩ := ha
  obtain ⟨e',he',rfl⟩ := ha'
  rw [point_transition]
  exact (contDiffGroupoid ω 𝓘(ℂ)).compatible he he'

end ProjectiveLineComplexAtlas318
