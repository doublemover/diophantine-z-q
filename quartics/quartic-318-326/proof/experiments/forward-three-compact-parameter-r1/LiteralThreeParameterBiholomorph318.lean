module
public import LiteralThreeCompactParameter318
public import ThreeCompactBranchOrders318
public import LiteralPlaneAmbientAnalytic318
public import LiteralPlaneBiholomorph318
public section
noncomputable section
open scoped Manifold ContDiff
namespace LiteralThreeParameterBiholomorph318
open ThreeCompactParameter318 LiteralThreeCompactParameter318
open ThreeArithmeticQuotient318 LiteralPlaneComparison318
set_option maxHeartbeats 0

lemma parameter_ambient_analytic {z x : ℂ} (hb : denominator z x ≠ 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => parameter p.1 p.2) (z,x) := by
  have hf : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (z,x) := analyticAt_fst
  have hs : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (z,x) := analyticAt_snd
  unfold parameter numerator denominator
  exact (analyticAt_const.mul (((hf.sub analyticAt_const).mul (hs.pow 2)).sub hf)).div
    ((analyticAt_const.mul hf).sub ((hf.sub analyticAt_const).mul (hs.pow 2))) hb

lemma parameter_open : IsOpen {t : ℂ | t ≠ 0 ∧ t+27 ≠ 0 ∧ t+243 ≠ 0 ∧ D t ≠ 0} := by
  exact (isOpen_ne_fun continuous_id continuous_const).inter
    ((isOpen_ne_fun (by fun_prop) continuous_const).inter
      ((isOpen_ne_fun (by fun_prop) continuous_const).inter
        (isOpen_ne_fun (by unfold D; fun_prop) continuous_const)))

lemma parameter_embedding : Topology.IsOpenEmbedding (fun t : ParameterOpen => t.val) :=
  parameter_open.isOpenEmbedding_subtypeVal

local instance : Nonempty ParameterOpen := ⟨⟨1,by norm_num [D]⟩⟩

/-- The natural complex open-subspace atlas, independent of the source map. -/
@[expose, instance_reducible] def parameterChartedSpace : ChartedSpace ℂ ParameterOpen :=
  parameter_embedding.singletonChartedSpace

lemma parameter_manifold :
    letI := parameterChartedSpace
    IsManifold 𝓘(ℂ) ω ParameterOpen := by
  letI := parameterChartedSpace
  exact parameter_embedding.isManifold_singleton

lemma parameter_inclusion_analytic :
    letI := parameterChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun t : ParameterOpen => t.val) := by
  letI := parameterChartedSpace
  exact contMDiff_isOpenEmbedding parameter_embedding

/-- Analyticity uses the independently proved ambient graph embedding of the
literal plane, then the actual rational formula with nonzero denominator. -/
theorem sourceParameter_scalar_analytic (N : ℕ) [NeZero N] :
    letI := AdmissibleJComplexAtlas318.complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun q : Source => (sourceParameter N q).val) := by
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  letI := LiteralPlaneJAtlas318.complexChartedSpace
  have hc := LiteralPlaneAmbientAnalytic318.coordinates_analytic.comp
    (LiteralPlaneBiholomorph318.comparison_analytic N)
  intro q
  let p := comparison N q
  have hb := denominator_ne_zero p.val.1.property.1 p.val.1.property.2 p.property
  have hp := (parameter_ambient_analytic hb).contDiffAt.comp_contMDiffAt
    (f := fun q : Source => LiteralPlaneJAtlas318.coordinates (comparison N q))
    (x := q) (hc q)
  exact hp

theorem sourceParameter_analytic (N : ℕ) [NeZero N] :
    letI := AdmissibleJComplexAtlas318.complexChartedSpace
    letI := parameterChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (sourceParameter N) := by
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  letI := parameterChartedSpace
  intro q
  apply contMDiffAt_iff_target.mpr
  refine ⟨(sourceParameter N).continuous.continuousAt,?_⟩
  exact sourceParameter_scalar_analytic N q

/-- In the original source j charts the inverse has coordinate J(T), which
is analytic at every point of the independently natural parameter open. -/
theorem sourceParameter_inverse_analytic (N : ℕ) [NeZero N] :
    letI := AdmissibleJComplexAtlas318.complexChartedSpace
    letI := parameterChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (sourceParameter N).symm := by
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  letI := parameterChartedSpace
  intro t
  apply contMDiffAt_iff_target.mpr
  refine ⟨(sourceParameter N).symm.continuous.continuousAt,?_⟩
  have he : extChartAt 𝓘(ℂ) ((sourceParameter N).symm t) ∘ (sourceParameter N).symm =
      (fun u : ParameterOpen => J u.val) := by
    funext u
    change AdmissibleJComplexAtlas318.localChart ((sourceParameter N).symm t)
      ((sourceParameter N).symm u)=J u.val
    rw [AdmissibleJComplexAtlas318.localChart_apply,sourceParameter_inverse_j]
  rw [he]
  exact (ThreeCompactBranchOrders318.J_analytic t.property.1).contDiffAt.comp_contMDiffAt
    (parameter_inclusion_analytic t)

/-- Full analytic equivalence on the unchanged admissible open. This still
does not identify the missing elliptic/cusp points with an actual compact source. -/
@[expose] def sourceBiholomorph (N : ℕ) [NeZero N] :
    letI := AdmissibleJComplexAtlas318.complexChartedSpace
    letI := parameterChartedSpace
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Source ParameterOpen ω := by
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  letI := parameterChartedSpace
  exact { toEquiv := (sourceParameter N).toEquiv
          contMDiff_toFun := sourceParameter_analytic N
          contMDiff_invFun := sourceParameter_inverse_analytic N }

end LiteralThreeParameterBiholomorph318
