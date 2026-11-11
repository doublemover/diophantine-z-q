module
public import FourRootAffineChangeCompletion318
public import FourRootNativeGermHolomorphy318
public import ComplexCurveHomeomorphInverse318
public section
noncomputable section
namespace FourRootAffineChangeHolomorphy318
open Set Filter FourRootNormalizedPointCharts318 FourRootAffineChangeCoordinates318
open FourRootAffineChangeCompletion318
open scoped Topology Manifold ContDiff

/-- Transfer from the inverse of an actual maximal chart. This uses the
whole neighborhood inverse, not just agreement on a parametrized subset. -/
theorem from_chart {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [TopologicalSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω N] (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (p : M) (hp : p ∈ e.source)
    (f : M → N) (hf : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z => f (e.symm z)) (e p)) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f p := by
  have hc := hf.comp p (contMDiffAt_of_mem_maximalAtlas he hp)
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  change f q=f (e.symm (e q))
  rw [e.left_inv hq]

variable (b c : Fin 4 → ℂ) (hb : Function.Injective b) (hc : Function.Injective c)
  (d r : ℂ) (hr : r ≠ 0) (h : ∀ i, c i = d+r^2*b i)
local instance : TopologicalSpace (Completed b) := FourRootGluedTopology318.topology b
local instance : TopologicalSpace (Completed c) := FourRootGluedTopology318.topology c
local instance : ChartedSpace ℂ (Completed b) := FourRootCompletedComplexAtlas318.chartedSpace b hb
local instance : ChartedSpace ℂ (Completed c) := FourRootCompletedComplexAtlas318.chartedSpace c hc
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed b) := FourRootCompletedComplexAtlas318.complex_manifold b hb
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed c) := FourRootCompletedComplexAtlas318.complex_manifold c hc

lemma finite_holomorphic (p : FinitePoints b) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (homeomorph b c d r hr h) (.inl p) := by
  let e := FourRootCompletedComplexAtlas318.finiteChart b hb p
  let e0 := FourRootFiniteComplexAtlas318.chart b hb p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed b) :=
    IsManifold.subset_maximalAtlas ⟨Sum.inl p,rfl⟩
  have hp : (.inl p : Completed b) ∈ e.source :=
    ⟨p,FourRootFiniteComplexAtlas318.chart_center b hb p,rfl⟩
  apply from_chart e he (.inl p) hp
  have ha : AnalyticAt ℂ (fun z => (e0.symm z).val) (e (.inl p)) := by
    rw [show e (.inl p)=e0 p from FourRootCompletedComplexAtlas318.finite_apply b hb p p]
    exact FourRootFiniteComplexAtlas318.inverse_analytic b hb p _
      (e0.map_source (FourRootFiniteComplexAtlas318.chart_center b hb p))
  let g : ℂ → FinitePoints c := fun z => finiteForward b c d r h (e0.symm z)
  have ht : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z => (g z).val.1) (e (.inl p)) := by
    exact contMDiffAt_iff_contDiffAt.mpr
      ((analyticAt_const.add (analyticAt_const.mul (analyticAt_fst.comp ha))).contDiffAt)
  have hz : ∀ i, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z => (g z).val.2 i) (e (.inl p)) := by
    intro i
    exact contMDiffAt_iff_contDiffAt.mpr
      ((analyticAt_const.mul (((ContinuousLinearMap.proj (R:=ℂ) i).analyticAt _).comp
        (analyticAt_snd.comp ha))).contDiffAt)
  exact FourRootNativeGermHolomorphy318.finite c hc g _ ht hz

lemma infinity_holomorphic (s : InfinitySigns) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (homeomorph b c d r hr h) (.inr s) := by
  let e := FourRootCompletedComplexAtlas318.infinityChart b s
  let e0 := FourRootInfinityComplexCharts318.chart b s
  let p := FourRootInfinityGraph318.center b s
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed b) :=
    IsManifold.subset_maximalAtlas ⟨Sum.inr s,rfl⟩
  have hp : (.inr s : Completed b) ∈ e.source :=
    ⟨p,FourRootInfinityComplexCharts318.chart_center b s,infinityChart_zero b s⟩
  have hep : e (.inr s)=e0 p := by
    rw [←infinityChart_zero b s]
    exact FourRootCompletedComplexAtlas318.infinity_apply b s p
  have hp0 : e0.symm (e (.inr s))=p := by
    rw [hep]
    exact e0.left_inv (FourRootInfinityComplexCharts318.chart_center b s)
  apply from_chart e he (.inr s) hp
  have ha : AnalyticAt ℂ (fun z => (e0.symm z).val) (e (.inr s)) := by
    rw [hep]
    exact FourRootInfinityComplexCharts318.inverse_analytic b s _
      (e0.map_source (FourRootInfinityComplexCharts318.chart_center b s))
  let g : ℂ → InfinityPoints c := fun z => infinityForward b c d r hr h (e0.symm z)
  have hg : g (e (.inr s))=FourRootInfinityGraph318.center c s := by
    dsimp [g]
    rw [hp0]
    apply Subtype.ext
    apply Prod.ext
    · exact zero_div r
    · rfl
  have hu : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z => (g z).val.1) (e (.inr s)) := by
    exact contMDiffAt_iff_contDiffAt.mpr
      (((analyticAt_fst.comp ha).div analyticAt_const hr).contDiffAt)
  have hs : ∀ i,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z => (g z).val.2 i) (e (.inr s)) := by
    intro i
    exact contMDiffAt_iff_contDiffAt.mpr
      ((((ContinuousLinearMap.proj (R:=ℂ) i).analyticAt _).comp (analyticAt_snd.comp ha)).contDiffAt)
  have hm := FourRootNativeGermHolomorphy318.infinity c hc g (e (.inr s)) s hg hu hs
  convert hm using 1
  funext z
  exact infinity_commutes b c d r hr h (e0.symm z)

/-- Whole holomorphy includes all finite ramification points and every
separate infinity sign. The independent atlases are not transported. -/
theorem holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (homeomorph b c d r hr h) := by
  intro p
  cases p with
  | inl p => exact finite_holomorphic b c hb hc d r hr h p
  | inr s => exact infinity_holomorphic b c hb hc d r hr h s

theorem inverse_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (homeomorph b c d r hr h).symm :=
  ComplexCurveHomeomorphInverse318.inverse _ (holomorphic b c hb hc d r hr h)
end FourRootAffineChangeHolomorphy318
