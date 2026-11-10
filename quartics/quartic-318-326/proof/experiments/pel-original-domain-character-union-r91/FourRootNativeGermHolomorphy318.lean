module
public import FourRootCompletedComplexAtlas318
public section
noncomputable section
namespace FourRootNativeGermHolomorphy318
open Set Filter
open scoped Topology Manifold ContDiff
open FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance : TopologicalSpace (Completed b):=FourRootGluedTopology318.topology b
local instance : ChartedSpace ℂ (Completed b):=FourRootCompletedComplexAtlas318.chartedSpace b hb
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed b):=FourRootCompletedComplexAtlas318.complex_manifold b hb
variable {M:Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ,ℂ) ω M]

/-- Native analytic coordinates imply holomorphy into the independent
completed atlas. The source may be the ORIGINAL curve, not just a disk.
Target continuity is derived from its inherited affine coordinates. -/
theorem finite (g:M→FinitePoints b) (x:M)
    (ht:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>(g y).val.1) x)
    (hz:∀k,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>(g y).val.2 k) x):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>finiteChart b (g y)) x:=by
  let e:=FourRootCompletedComplexAtlas318.finiteChart b hb (g x)
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed b):=
    IsManifold.subset_maximalAtlas ⟨Sum.inl (g x),rfl⟩
  have hp:finiteChart b (g x)∈e.source:=
    ⟨g x,FourRootFiniteComplexAtlas318.chart_center b hb (g x),rfl⟩
  have hc:ContinuousAt g x:=
    (ht.continuousAt.prodMk (continuousAt_pi.mpr (fun k=>(hz k).continuousAt))).subtype_mk _
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hp).mpr
  refine ⟨((FourRootGluedTopology318.finiteChart_continuous b).continuousAt.comp hc).continuousWithinAt,?_⟩
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>e (finiteChart b (g y))) x:=by
    obtain ⟨j,hj⟩:=FourRootFiniteComplexAtlas318.chart_axis b hb (g x)
    cases j with
    | none=>
      convert ht using 1
      funext y
      exact (FourRootCompletedComplexAtlas318.finite_apply b hb (g x) (g y)).trans (hj _)
    | some k=>
      convert hz k using 1
      funext y
      exact (FourRootCompletedComplexAtlas318.finite_apply b hb (g x) (g y)).trans (hj _)
  exact hh.contMDiffWithinAt

/-- At a genuine infinity sign point the actual target chart is u.
The three ratios are retained in the continuity proof, so the result
cannot merge distinct infinity points or omit their neighborhoods. -/
theorem infinity (g:M→InfinityPoints b) (x:M) (s:InfinitySigns)
    (hx:g x=FourRootInfinityGraph318.center b s)
    (hu:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>(g y).val.1) x)
    (hs:∀k,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>(g y).val.2 k) x):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>infinityChart b (g y)) x:=by
  let e:=FourRootCompletedComplexAtlas318.infinityChart b s
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed b):=
    IsManifold.subset_maximalAtlas ⟨Sum.inr s,rfl⟩
  have hp:infinityChart b (g x)∈e.source:=by
    refine ⟨g x,?_,rfl⟩
    rw [hx]
    exact FourRootInfinityComplexCharts318.chart_center b s
  have hc:ContinuousAt g x:=
    (hu.continuousAt.prodMk (continuousAt_pi.mpr (fun k=>(hs k).continuousAt))).subtype_mk _
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hp).mpr
  refine ⟨((FourRootGluedTopology318.infinityChart_continuous b).continuousAt.comp hc).continuousWithinAt,?_⟩
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>e (infinityChart b (g y))) x:=by
    convert hu using 1
    funext y
    exact (FourRootCompletedComplexAtlas318.infinity_apply b s (g y)).trans
      (FourRootInfinityComplexCharts318.chart_axis b s (g y))
  exact hh.contMDiffWithinAt
end FourRootNativeGermHolomorphy318
