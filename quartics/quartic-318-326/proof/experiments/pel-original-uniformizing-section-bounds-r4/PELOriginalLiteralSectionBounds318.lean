module
public import LiteralContactUniformizingData318
public import PELOriginalLiteralPoincare318
public section
noncomputable section
namespace PELOriginalLiteralSectionBounds318
open FourRootNormalizedPointCharts318 LiteralMetricExtension318
open PELOriginalManuscriptNormalization318 PELOriginalLiteralContactScaling318
open PELUnlevelledComplexBase318
open scoped Topology Manifold ContDiff
local instance : TopologicalSpace (Completed contacts) := FourRootGluedTopology318.topology contacts
local instance : ChartedSpace ℂ (Completed contacts) := FourRootCompletedComplexAtlas318.chartedSpace contacts contacts_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed contacts) := FourRootCompletedComplexAtlas318.complex_manifold contacts contacts_injective
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable (hλ : lambda=2401) (hμ : mu= -343/32)

/-- Actual quantitative-data producer for the original numerical curve.
The explicit numerical identification remains the only additional
geometric input at this analytic metric stage. -/
@[expose] def metricData : UniformizingSectionBounds318.Data (Completed contacts) :=
  LiteralContactUniformizingData318.uniformizingData (literalComparison hλ hμ)
    (forward_holomorphic hλ hμ) (inverse_holomorphic hλ hμ)

/-- Exact published bound for the two literal J-squared-scaled analytic
quadratic sections at EVERY actual curve point, including branch and
infinity points, under the explicitly retained original branch identities.
This does not identify an arithmetic Hodge/KS frame with that metric. -/
theorem integral_section_norms (p : Completed contacts) :
    PeterssonSectionNorm318.quadraticNorm
      (HolomorphicPoincare318.coefficient ((metricData hλ hμ).uniformizer p) (0,0))
      ((2765952000:ℂ)^2*SectionCoefficientBounds318.Chart.section0 ((metricData hλ hμ).kind p))≤
      (2765952000:ℝ)^2*(4*12540153541944538512) ∧
    PeterssonSectionNorm318.quadraticNorm
      (HolomorphicPoincare318.coefficient ((metricData hλ hμ).uniformizer p) (0,0))
      ((2765952000:ℂ)^2*SectionCoefficientBounds318.Chart.section1 ((metricData hλ hμ).kind p))≤
      (2765952000:ℝ)^2*(4*12540153541944538512) := by
  letI : CompactSpace (Completed contacts) := literal_compact hλ hμ
  letI : Nonempty (Completed contacts) := ⟨p⟩
  exact (metricData hλ hμ).integral_section_norms p
end PELOriginalLiteralSectionBounds318
