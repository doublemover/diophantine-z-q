module
public import PELOriginalConstructedSphereFilling318
public section
noncomputable section
namespace PELOriginalFiniteBranchRemoval318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonOriginalPoints318 PELActualEdgeHalfNeighborhood318
open PELOriginalConformalComparisonInputs318 PELOriginalBoundedSeamCoordinate318
open PELOriginalConstructedSphereFilling318 ComplexSphereCharts318 ReflectedDiskJoukowski318
local instance : ChartedSpace ℂ MaximalBase := maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ) := sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := sphere_manifold

/-- Any ADDITIONAL finite branch exceptions are removable using the
already constructed punctured-map continuity. This works in the original
arithmetic atlas and avoids assuming analytic descent through a square
chart. No continuity at the remaining corners is needed. -/
theorem holomorphic_outside_corners
    (F:MaximalBase→OnePoint ℂ)
    (hcont:∀q∉cornerOrbits,ContinuousAt F q)
    (E:Set MaximalBase) (hE:E.Finite)
    (hhol:∀q∉E,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q) :
    ∀q∉cornerOrbits,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q := by
  intro p hp
  apply ComplexCurveRemovablePoints318.removable_at F (hcont p hp)
  have hfinite:(E\{p}).Finite:=hE.subset diff_subset
  have hnb:(E\{p})ᶜ∈𝓝 p:=hfinite.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnb,self_mem_nhdsWithin]
    with q hq hqp
  exact hhol q (fun he=>hq ⟨he,hqp⟩)

/-- Final original-atlas sphere comparison from a genuine continuous
punctured quotient map, holomorphic away from ANY proved finite branch
exception set, with its exact interior and regular edge formulas.
Additional branch points and all remaining corners are filled by the
actual analytic removability arguments, not supplied as hypotheses. -/
theorem sphere_from_punctured_descent
    (F:MaximalBase→OnePoint ℂ)
    (hcont:∀q∉cornerOrbits,ContinuousAt F q)
    (E:Set MaximalBase) (hE:E.Finite)
    (hhol:∀q∉E,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q)
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=Metric.ball 0 1) (ha:InteriorAgreement F e)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=joukowski w) :
    ∃H:MaximalBase≃ₜOnePoint ℂ,
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      (∀q∉cornerOrbits,H q=F q) ∧ InteriorAgreement H e :=
  exists_original_biholomorphic_sphere F (holomorphic_outside_corners F hcont E hE hhol)
    e hs ht ha hedge
end PELOriginalFiniteBranchRemoval318
