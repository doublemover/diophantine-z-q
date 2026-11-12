module
public import ProjectiveLineStandardSphereComparison318
public import PELOriginalAnalyticSphere318
public section
noncomputable section
namespace PELOriginalProjectiveLineComparison318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonOriginalPoints318
open PELOriginalConformalComparisonInputs318 PELActualInteriorSphereMap318
open ProjectiveLineComplexSchemePoints318 ProjectiveLineIndependentPointTopology318
open ProjectiveLineIndependentComplexAtlas318 ProjectiveLineStandardSphereComparison318
open ComplexSphereCharts318 QuaternionicJointPeriodTopology318
local instance : TopologicalSpace SchemePoints:=pointTopology
local instance : ChartedSpace ℂ SchemePoints:=pointCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω SchemePoints:=complex_manifold
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- The ORIGINAL maximal arithmetic complex curve is compared with the
actual complex Scheme-valued points of homogeneous Proj P1, on the
independently specified polynomial-chart topology and complex atlas.
The same genuine interior formula is retained as a Scheme point.
This analytic comparison alone does not assert arithmetic algebraization
or a particular rational normalization of the five branch images. -/
theorem original_projective_line_comparison :
    ∃H:MaximalBase≃ₜSchemePoints,
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      ∃e:OpenPartialHomeomorph ℂ ℂ,e.source=openDomain ∧ e.target=Metric.ball 0 1 ∧
        ∀τ:HalfPlane,(τ:ℂ)∈openDomain →
          H (maximalProjection τ)=spherePoint (sphereMap e τ) := by
  obtain ⟨H,hH,hI,e,hs,ht,ha⟩:=PELOriginalAnalyticSphere318.original_analytic_sphere
  refine ⟨H.trans sphereSchemeHomeomorph,?_,?_,e,hs,ht,?_⟩
  · exact sphereSchemeHomeomorph_biholomorphic.1.comp hH
  · exact hI.comp sphereSchemeHomeomorph_biholomorphic.2
  · intro τ hτ
    exact congrArg spherePoint (ha τ hτ)
end PELOriginalProjectiveLineComparison318
