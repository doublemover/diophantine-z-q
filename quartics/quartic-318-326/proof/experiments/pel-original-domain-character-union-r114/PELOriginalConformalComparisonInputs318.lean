module
public import PELOriginalOpenDenseInterior318
public import ComplexCurveDenseComparison318
public section
noncomputable section
namespace PELOriginalConformalComparisonInputs318
open Set
open scoped OnePoint
open QuaternionicJointPeriodTopology318 PELMaximalActualComplexDomain318
open PELMaximalHalfOctagonOriginalPoints318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonShape318 PELOriginalMaximalQuotient318
open PELOriginalOpenDenseInterior318 PELActualInteriorSphereMap318 ComplexSphereRegularTarget318
set_option maxHeartbeats 2200000

/-- The exact unchanged original interior formula a descended map must
satisfy. No old radial sphere parameterization is substituted. -/
@[expose] def InteriorAgreement (F : MaximalBase → OnePoint ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) : Prop :=
  ∀ τ : HalfPlane,(τ:ℂ)∈openDomain → F (maximalProjection τ)=sphereMap e τ

/-- Genuine conformal interior injectivity yields injectivity of the
actual descended map on its original dense open arithmetic interior. -/
theorem original_interior_injective (F : MaximalBase → OnePoint ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) (hs : e.source=openDomain)
    (ht : e.target=Metric.ball 0 1) (ha : InteriorAgreement F e) : InjOn F originalInterior := by
  rintro q ⟨τ,hτ,rfl⟩ r ⟨σ,hσ,rfl⟩ he
  rw [ha τ hτ,ha σ hσ] at he
  have hc := sphereMap_injective e hs ht hτ hσ he
  exact congrArg maximalProjection (Subtype.ext hc)

/-- The same original interior formula already covers the explicit dense
regular sphere target. Compactness is not used to assume this coverage. -/
theorem original_regular_coverage (F : MaximalBase → OnePoint ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) (hs : e.source=openDomain)
    (ht : e.target=Metric.ball 0 1) (ha : InteriorAgreement F e) : regular⊆range F := by
  intro p hp
  obtain ⟨z,hz,hzp⟩ := actual_interior_cover e hs ht p hp
  refine ⟨maximalProjection ⟨z,hz.1⟩,?_⟩
  rw [ha ⟨z,hz.1⟩ hz]
  exact hzp

/-- Exhaustive original half-cut coverage turns the actual boundary
image exclusion into the necessary ALL-preimages condition. This is
not inferred merely from injectivity or coverage of the interior. -/
theorem original_regular_preimage (F : MaximalBase → OnePoint ℂ)
    (hb : ∀ P : upperCut,(upperCutCenter P).val∉strictPolygon →
      F (cutProjection P)∉regular) : F ⁻¹' regular⊆originalInterior := by
  intro q hq
  obtain ⟨P,rfl⟩ := PELMaximalHalfOctagonBoundaryAction318.cutProjection_surjective q
  by_cases hs : (upperCutCenter P).val∈strictPolygon
  · exact cut_originalInterior P hs
  · exact False.elim (hb P hs hq)
end PELOriginalConformalComparisonInputs318
