module
public import PELActualCompactConformalSphere318
public import PELActualConformalMirror318
public section
noncomputable section
namespace PELOriginalAnalyticSphere318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELMaximalActualComplexDomain318 PELActualCanonicalBoundary318
open PELOriginalConformalComparisonInputs318 ComplexSphereCharts318
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- The exact normalized interior producer is consumed on its ORIGINAL
source. All remaining analytic boundary and arithmetic quotient inputs
are supplied by the constructed compact comparison. This is a source
proof dependency on the full Riemann-mapping port, NOT an assertion that
that port or this endpoint has already passed hosted Lean. -/
theorem original_analytic_sphere :
    ∃H:MaximalBase≃ₜOnePoint ℂ,
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      ∃e:OpenPartialHomeomorph ℂ ℂ,e.source=openDomain ∧
        e.target=Metric.ball 0 1 ∧ InteriorAgreement H e := by
  obtain ⟨e,hs,ht,_,he,_,_,_,hm⟩:=PELActualConformalMirror318.actual_symmetric_conformal_chart
  obtain ⟨H,hH,hI,_,ha⟩:=PELActualCompactConformalSphere318.actual_compact_biholomorphic_sphere
    e hs ht he hm
  exact ⟨H,hH,hI,e,hs,ht,ha⟩
end PELOriginalAnalyticSphere318
