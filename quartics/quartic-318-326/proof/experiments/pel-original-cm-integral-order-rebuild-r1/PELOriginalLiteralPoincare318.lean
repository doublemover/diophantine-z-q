module
public import PELOriginalLiteralContactScaling318
public import OriginalUniformizedCurveAtlas318
public section
noncomputable section
namespace PELOriginalLiteralPoincare318
open Set Filter FourRootNormalizedPointCharts318 LiteralMetricExtension318
open PELOriginalManuscriptNormalization318 PELOriginalLiteralContactScaling318
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318 PELUnlevelledComplexBase318
open scoped Topology Manifold ContDiff
local instance : TopologicalSpace (Completed contacts) := FourRootGluedTopology318.topology contacts
local instance : ChartedSpace ℂ (Completed contacts) := FourRootCompletedComplexAtlas318.chartedSpace contacts contacts_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed contacts) := FourRootCompletedComplexAtlas318.complex_manifold contacts contacts_injective
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable (hλ : lambda=2401) (hμ : mu= -343/32)

@[expose] def coefficient (e : OpenPartialHomeomorph (Completed contacts) ℂ)
    (p : Completed contacts) : ℝ :=
  OriginalUniformizedCurveAtlas318.coefficient (literalComparison hλ hμ) e p

/-- Literal numerical target charts now have the actual original
Poincare coefficients, with no independently assumed metric or curvature. -/
theorem positive_continuous (e : OpenPartialHomeomorph (Completed contacts) ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed contacts)) :
    (∀ p ∈ e.source,0<coefficient hλ hμ e p) ∧ ContinuousOn (coefficient hλ hμ e) e.source :=
  ⟨fun p hp => OriginalUniformizedCurveAtlas318.coefficient_positive
      (literalComparison hλ hμ) (forward_holomorphic hλ hμ) (inverse_holomorphic hλ hμ) e p hp he,
    OriginalUniformizedCurveAtlas318.coefficient_continuousOn
      (literalComparison hλ hμ) (forward_holomorphic hλ hμ) (inverse_holomorphic hλ hμ) e he⟩

/-- Actual numerical completed-chart uniformizers and their ENTIRE local
metric equality, including every branch and all eight infinity points.
The two parameter identities, equivalently the prior four j premises,
remain explicit; this is not an unconditional numerical identification. -/
theorem exists_uniformizer (e : OpenPartialHomeomorph (Completed contacts) ℂ)
    (p : Completed contacts) (hp : p ∈ e.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed contacts)) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ 0<(f 0).im ∧ deriv f 0≠0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ),0<(f z).im ∧
        literalComparison hλ hμ (projection (baseChart.symm (f z)))=e.symm (e p+z)) ∧
      (∀ᶠ z in 𝓝 (0 : ℂ),coefficient hλ hμ e (e.symm (e p+z))=
        MobiusPoincarePullback318.density f z) :=
  OriginalUniformizedCurveAtlas318.exists_uniformizer_with_metric
    (literalComparison hλ hμ) (forward_holomorphic hλ hμ) (inverse_holomorphic hλ hμ) e p hp he
end PELOriginalLiteralPoincare318
