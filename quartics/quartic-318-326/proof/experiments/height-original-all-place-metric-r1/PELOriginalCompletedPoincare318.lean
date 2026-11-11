module
public import PELOriginalPoincareContinuity318
public import PELOriginalCompletedContactBiholomorph318
public import HolomorphicHomeomorphChartTransport318
public section
noncomputable section
namespace PELOriginalCompletedPoincare318
open Set Filter
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactBiholomorph318 FourRootNormalizedPointCharts318
open PELOriginalChartUniformizer318 PELOriginalPoincareAtlas318 PELOriginalPoincareContinuity318
open scoped Topology Manifold ContDiff
local instance : TopologicalSpace (Completed branches) := FourRootGluedTopology318.topology branches
local instance : ChartedSpace ℂ (Completed branches) :=
  FourRootCompletedComplexAtlas318.chartedSpace branches branches_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed branches) :=
  FourRootCompletedComplexAtlas318.complex_manifold branches branches_injective
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

@[expose] def sourceChart (e : OpenPartialHomeomorph (Completed branches) ℂ) :
    OpenPartialHomeomorph UnlevelledBase ℂ := comparison.toOpenPartialHomeomorph.trans e

lemma sourceChart_maximal (e : OpenPartialHomeomorph (Completed branches) ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed branches)) :
    sourceChart e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase :=
  HolomorphicHomeomorphChartTransport318.maximal comparison forward_holomorphic inverse_holomorphic e he

lemma sourceChart_center (e : OpenPartialHomeomorph (Completed branches) ℂ)
    (p : Completed branches) (hp : p ∈ e.source) : comparison.symm p ∈ (sourceChart e).source :=
  ⟨Set.mem_univ _,by simpa only [comparison.apply_symm_apply] using hp⟩
lemma sourceChart_value (e : OpenPartialHomeomorph (Completed branches) ℂ) (p : Completed branches) :
    sourceChart e (comparison.symm p) = e p := by
  change e (comparison (comparison.symm p)) = _
  rw [comparison.apply_symm_apply]
lemma sourceChart_inverse (e : OpenPartialHomeomorph (Completed branches) ℂ) (z : ℂ) :
    comparison ((sourceChart e).symm z) = e.symm z := comparison.apply_symm_apply _

/-- Actual upper-half-plane uniformizers for every independent completed
four-root chart, including all finite branch and eight infinity charts.
The full original PEL comparison square is retained. -/
theorem exists_original_uniformizer (e : OpenPartialHomeomorph (Completed branches) ℂ)
    (p : Completed branches) (hp : p ∈ e.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed branches)) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ 0 < (f 0).im ∧ deriv f 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ),0 < (f z).im ∧
        comparison (projection (baseChart.symm (f z))) = e.symm (e p + z) := by
  obtain ⟨f,hf,hu,hd,hs⟩ := exists_uniformizer (sourceChart e) (comparison.symm p)
    (sourceChart_center e p hp) (sourceChart_maximal e he)
  refine ⟨f,hf,hu,hd,?_⟩
  filter_upwards [hs] with z hz
  refine ⟨hz.1,?_⟩
  rw [hz.2,sourceChart_value,sourceChart_inverse]

@[expose] def coefficient (e : OpenPartialHomeomorph (Completed branches) ℂ)
    (p : Completed branches) : ℝ := chartDensity (sourceChart e) (comparison.symm p)

/-- Positive and continuous hyperbolic coefficients on the SAME independently
constructed completed four-root curve. Numeric branch constants are not assumed. -/
theorem coefficient_positive_continuous (e : OpenPartialHomeomorph (Completed branches) ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed branches)) :
    (∀ p ∈ e.source,0 < coefficient e p) ∧ ContinuousOn (coefficient e) e.source := by
  constructor
  · intro p hp
    exact chartDensity_positive (sourceChart e) (comparison.symm p)
      (sourceChart_center e p hp) (sourceChart_maximal e he)
  · exact (chartDensity_continuousOn (sourceChart e) (sourceChart_maximal e he)).comp
      comparison.symm.continuous.continuousOn (fun p hp => sourceChart_center e p hp)
end PELOriginalCompletedPoincare318
