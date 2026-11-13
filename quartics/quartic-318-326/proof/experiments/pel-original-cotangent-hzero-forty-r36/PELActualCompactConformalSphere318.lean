module
public import PELActualPuncturedHolomorphy318
public import PELOriginalFiniteBranchRemoval318
public section
noncomputable section
namespace PELActualCompactConformalSphere318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open QuaternionicJointPeriodTopology318 PELMaximalActualComplexDomain318
open PELActualCanonicalBoundary318 PELActualPuncturedQuotientMap318 PELActualAmbientProjection318
open PELActualPuncturedHolomorphy318 PELActualEdgeHalfNeighborhood318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELOriginalConstructedSphereFilling318 PELOriginalBoundedSeamCoordinate318
open PELOriginalConformalComparisonInputs318 ComplexSphereCharts318
set_option maxHeartbeats 3200000
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- Restrict the genuine conformal partial homeomorphism, retaining its
actual function and inverse. No radial/topological disk map is substituted. -/
@[expose] def diskOfChart (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=Metric.ball 0 1) :
    openDomain≃ₜConformalBoundaryModulus318.UnitDisk where
  toFun z:=⟨e z,ht ▸ e.map_source (hs.symm ▸ z.property)⟩
  invFun w:=⟨e.symm w,hs ▸ e.map_target (ht.symm ▸ w.property)⟩
  left_inv z:=Subtype.ext (e.left_inv (hs.symm ▸ z.property))
  right_inv w:=Subtype.ext (e.right_inv (ht.symm ▸ w.property))
  continuous_toFun:=by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (e.continuousAt (hs.symm ▸ z.property)).comp continuous_subtype_val.continuousAt
  continuous_invFun:=by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (e.continuousAt_symm (ht.symm ▸ w.property)).comp continuous_subtype_val.continuousAt

theorem cornerImages_eq : cornerImages=cornerOrbits := rfl

/-- The completed analytic comparison is now CONSTRUCTED from a genuine
symmetric interior conformal chart. All boundary traces, actual arithmetic
collar descent, finite branch removal, bounded corner limits, whole-map
continuity, global injectivity and inverse holomorphy are produced by the
preceding joins. The original interior chart existence remains separate. -/
theorem actual_compact_biholomorphic_sphere
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=Metric.ball 0 1) (he:AnalyticOnNhd ℂ e openDomain)
    (hm:∀z∈openDomain,e (J z)=J (e z)) :
    ∃H:MaximalBase≃ₜOnePoint ℂ,
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      (∀q∉cornerOrbits,H q=totalMap e q) ∧ InteriorAgreement H e := by
  let disk:=diskOfChart e hs ht
  have hf:∀q:openDomain,e q=(disk q).val:=fun _=>rfl
  have hcont:∀q∉cornerOrbits,ContinuousAt (totalMap e) q := by
    intro q hq
    exact totalMap_continuousAt disk e hf he hm hq
  have hhol:∀q∉exceptions,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (totalMap e) q :=
    actual_punctured_holomorphic disk e hf he hm
  have hinterior:InteriorAgreement (totalMap e) e := by
    intro τ hτ
    have hsafe:ambientProjection τ∈regularBase := by
      rw [ambientProjection_upper]
      exact interior_not_cornerOrbits ⟨τ,hτ,rfl⟩
    have h:=ambientMap_interior disk e hf he hm hτ hsafe
    simpa only [ambientMap,Function.comp_apply,ambientProjection_upper,
      PELActualInteriorSphereMap318.sphereMap] using h
  have hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ totalMap e (cutProjection P)=ReflectedDiskJoukowski318.joukowski w := by
    intro P i hi
    have hsaf:cutProjection P∈regularBase:=regular_not_cornerOrbits P i hi
    let Q:regularCut:=⟨P,hsaf⟩
    have hclosed:=original_noncorner Q
    have hnot:(cutPoint P:ℂ)∉openDomain := by
      intro ho
      have hp:=((original_domain_iff _).mp ho).2 i
      rw [hi.2.1] at hp
      exact (lt_irrefl (0:ℝ)) hp
    exact ⟨trace e (cutPoint P),trace_unit_on_boundary disk e hf he hclosed hnot,
      totalMap_agrees disk e hf he hm Q⟩
  exact PELOriginalFiniteBranchRemoval318.sphere_from_punctured_descent
    (totalMap e) hcont exceptions exceptions_finite hhol e hs ht hinterior hedge
end PELActualCompactConformalSphere318
