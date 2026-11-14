module
public import LegendreNativeGermHolomorphy318
public section
noncomputable section
namespace LegendreCurveFiniteGermHolomorphy318
open Set Filter
open scoped Topology Manifold ContDiff
open LegendrePlaneOverlap318
variable (l:ℂ) [Fact (l≠0 ∧ l≠1)]
local instance : ChartedSpace ℂ (CompletedPlane l):=LegendreCompletedComplexAtlas318.chartedSpace l
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CompletedPlane l):=LegendreCompletedComplexAtlas318.complex_manifold l
variable {M:Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]

/-- Native finite-coordinate holomorphy for an arbitrary GIVEN source
complex curve, in the independent completed target atlas. -/
theorem finite (g:M→LegendreFiniteComplexAtlas318.Plane l) (p:M)
    (hx:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q=>(g q).val.1) p)
    (hy:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q=>(g q).val.2) p):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q=>finiteChart l (g q)) p:=by
  let e:=LegendreCompletedComplexAtlas318.finiteChart l (g p)
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CompletedPlane l):=
    IsManifold.subset_maximalAtlas ⟨Sum.inl (g p),rfl⟩
  have hp:finiteChart l (g p)∈e.source:=
    ⟨g p,LegendreFiniteComplexAtlas318.chart_center l (g p),rfl⟩
  have hc:ContinuousAt g p:=(hx.continuousAt.prodMk hy.continuousAt).subtype_mk _
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hp).mpr
  refine ⟨((finite_open l).continuous.continuousAt.comp hc).continuousWithinAt,?_⟩
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q=>e (finiteChart l (g q))) p:=by
    rcases LegendreFiniteComplexAtlas318.chart_axis l (g p) with ha|ha
    · convert hx using 1
      funext q
      exact (LegendreCompletedComplexAtlas318.finite_apply l (g p) (g q)).trans (ha _)
    · convert hy using 1
      funext q
      exact (LegendreCompletedComplexAtlas318.finite_apply l (g p) (g q)).trans (ha _)
  exact hh.contMDiffWithinAt
end LegendreCurveFiniteGermHolomorphy318
