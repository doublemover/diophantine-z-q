module
public import ThreeJChartHolomorphy318
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public section
noncomputable section
open Function Filter Topology
open scoped Manifold ContDiff
namespace ThreeJManifoldHolomorphy318
open ProjectiveLineFieldPoints318 ProjectiveLineComplexTopology318 ProjectiveLineComplexAtlas318
open SphereCharts318 SphereComplexCurve318 ThreeProjectiveJPoints318 ThreeJChartHolomorphy318
open ActualThreeProjectivePoints318 ActualThreeCompactJPoints318 ActualThreeComplexAtlas318

local instance : TopologicalSpace ComplexPoints := complexPointTopology
local instance : ChartedSpace ℂ ComplexPoints := pointChartedSpace
local instance : IsManifold 𝓘(ℂ) ω ComplexPoints := point_isManifold

/-- Index the existing two analytic point charts by their original algebraic
chart indices. No replacement atlas or new topology is introduced. -/
@[expose] def evaluationChart : Fin 2 → OpenPartialHomeomorph ComplexPoints ℂ :=
  Fin.cases (pointChart infinityChart) (fun _ => pointChart finiteChart)

lemma evaluationChart_symm (i : Fin 2) (t : ℂ) :
    (evaluationChart i).symm t=chartPoint (R:=ℚ) i t := by
  fin_cases i
  · exact infinity_pointChart_symm t
  · exact finite_pointChart_symm t

lemma evaluationChart_target (i : Fin 2) : (evaluationChart i).target=Set.univ := by
  fin_cases i
  · exact infinity_target
  · exact finite_target

lemma evaluationChart_maximal (i : Fin 2) :
    evaluationChart i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ComplexPoints := by
  apply IsManifold.subset_maximalAtlas
  fin_cases i
  · exact ⟨infinityChart,Or.inr rfl,rfl⟩
  · exact ⟨finiteChart,Or.inl rfl,rfl⟩

lemma evaluationChart_symm_contMDiff (i : Fin 2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (evaluationChart i).symm := by
  intro t
  exact contMDiffAt_symm_of_mem_maximalAtlas (evaluationChart_maximal i)
    (by rw [evaluationChart_target]; trivial)

/-- An exact analytic representative on an original source chart implies
manifold holomorphy at its genuine scheme-valued point. Source and target
inverse-chart maps and their local inverse identities are explicitly used. -/
theorem contMDiffAt_of_expression (i : Fin 2) (t : ℂ)
    (h : HasAnalyticChartExpression i t) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω mapPoints (chartPoint (R:=ℚ) i t) := by
  obtain ⟨j,F,hF,hEq⟩ := h
  have hF' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F t :=
    contMDiffAt_iff_contDiffAt.mpr hF.contDiffAt
  have hlocal : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (mapPoints ∘ (evaluationChart i).symm) t := by
    apply ((evaluationChart_symm_contMDiff j (F t)).comp t hF').congr_of_eventuallyEq
    filter_upwards [hEq] with z hz
    change mapPoints ((evaluationChart i).symm z)=(evaluationChart j).symm (F z)
    rw [evaluationChart_symm,evaluationChart_symm]
    exact hz
  have ht : t ∈ (evaluationChart i).target := by rw [evaluationChart_target]; trivial
  have hp : chartPoint (R:=ℚ) i t ∈ (evaluationChart i).source := by
    rw [←evaluationChart_symm]
    exact (evaluationChart i).map_target ht
  have hv : evaluationChart i (chartPoint (R:=ℚ) i t)=t := by
    rw [←evaluationChart_symm]
    exact (evaluationChart i).right_inv ht
  have hsource : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (evaluationChart i)
      (chartPoint (R:=ℚ) i t) :=
    contMDiffAt_of_mem_maximalAtlas (evaluationChart_maximal i) hp
  have hlocal' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (mapPoints ∘ (evaluationChart i).symm)
      (evaluationChart i (chartPoint (R:=ℚ) i t)) := by rwa [hv]
  apply (hlocal'.comp _ hsource).congr_of_eventuallyEq
  filter_upwards [(evaluationChart i).open_source.mem_nhds hp] with p hp'
  simp only [Function.comp_apply,(evaluationChart i).left_inv hp']

/-- Holomorphy of the exact global scheme j action for the actual original
complex chart structure on its genuine scheme-valued points. -/
theorem mapPoints_contMDiff : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω mapPoints := by
  intro p
  obtain ⟨i,t,hp,h⟩ := every_point_analytic p
  rw [←hp]
  exact contMDiffAt_of_expression i t h

/-- The exact scheme-induced compact modular j map is holomorphic for the
already identified original orbit/q-disc analytic structure. -/
theorem compactJ_contMDiff :
    letI := filledChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω compactJ := by
  letI := filledChartedSpace
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω compactPointHomeomorph :=
    compactPointBiholomorph.contMDiff
  exact mapPoints_contMDiff.comp h

end ThreeJManifoldHolomorphy318
