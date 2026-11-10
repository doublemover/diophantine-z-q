module
public import PELOriginalConformalComparisonInputs318
public import PELMaximalComplexAtlas318
public section
noncomputable section
namespace PELOriginalGlobalConformalComparison318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonShape318
open PELMaximalHalfOctagonOriginalPoints318 PELOriginalOpenDenseInterior318
open PELOriginalConformalComparisonInputs318 ComplexSphereRegularTarget318 ComplexSphereCharts318
local instance : ChartedSpace ℂ MaximalBase := maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ) := sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := sphere_manifold

/-- The final comparison on the ORIGINAL arithmetic complex curve.
All open/dense, interior-injectivity, target-density and coverage inputs
are now produced. The remaining geometric inputs are explicitly the
same filled map's holomorphy, exact conformal interior formula and actual
boundary-image exclusion. No comparison map is defined by transporting
an arbitrary topological complex structure. -/
@[expose] def originalSphereComparison (F : MaximalBase → OnePoint ℂ)
    (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (e : OpenPartialHomeomorph ℂ ℂ) (hs : e.source=openDomain)
    (ht : e.target=Metric.ball 0 1) (ha : InteriorAgreement F e)
    (hb : ∀ P : upperCut,(upperCutCenter P).val∉strictPolygon → F (cutProjection P)∉regular) :
    MaximalBase ≃ₜ OnePoint ℂ :=
  ComplexCurveDenseComparison318.comparison F hF originalInterior
    originalInterior_open originalInterior_dense (original_interior_injective F e hs ht ha)
    regular regular_dense (original_regular_coverage F e hs ht ha) (original_regular_preimage F hb)

theorem originalSphereComparison_biholomorphic (F : MaximalBase → OnePoint ℂ)
    (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (e : OpenPartialHomeomorph ℂ ℂ) (hs : e.source=openDomain)
    (ht : e.target=Metric.ball 0 1) (ha : InteriorAgreement F e)
    (hb : ∀ P : upperCut,(upperCutCenter P).val∉strictPolygon → F (cutProjection P)∉regular) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalSphereComparison F hF e hs ht ha hb) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalSphereComparison F hF e hs ht ha hb).symm :=
  ComplexCurveDenseComparison318.comparison_biholomorphic F hF originalInterior
    originalInterior_open originalInterior_dense (original_interior_injective F e hs ht ha)
    regular regular_dense (original_regular_coverage F e hs ht ha) (original_regular_preimage F hb)
end PELOriginalGlobalConformalComparison318
