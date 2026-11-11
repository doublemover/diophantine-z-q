module
public import PELOriginalBoundaryClosedPropagation318
public import PELOriginalGlobalConformalComparison318
public section
noncomputable section
namespace PELOriginalUnitTraceComparison318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonOriginalPoints318 PELActualEdgeHalfNeighborhood318
open PELOriginalConformalComparisonInputs318 ComplexSphereCharts318
open PELOriginalGlobalConformalComparison318 PELOriginalBoundaryClosedPropagation318
local instance : ChartedSpace ℂ MaximalBase := maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ) := sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := sphere_manifold

/-- Original-atlas global comparison from the actual filled holomorphic
map and its constructed interior/regular-edge formulas. The all-boundary
exclusion, including the six corners, is now produced rather than assumed. -/
@[expose] def comparison (F:MaximalBase→OnePoint ℂ)
    (hF:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=Metric.ball 0 1) (ha:InteriorAgreement F e)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=ReflectedDiskJoukowski318.joukowski w) :
    MaximalBase≃ₜOnePoint ℂ :=
  originalSphereComparison F hF e hs ht ha
    (original_boundary_exclusion_of_unit_traces F hF.continuous hedge)

theorem comparison_biholomorphic (F:MaximalBase→OnePoint ℂ)
    (hF:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=Metric.ball 0 1) (ha:InteriorAgreement F e)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=ReflectedDiskJoukowski318.joukowski w) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison F hF e hs ht ha hedge) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison F hF e hs ht ha hedge).symm :=
  originalSphereComparison_biholomorphic F hF e hs ht ha
    (original_boundary_exclusion_of_unit_traces F hF.continuous hedge)
end PELOriginalUnitTraceComparison318
