module
public import PELJointHolomorphicLift318
public section
noncomputable section
namespace PELJointOrderEndomorphisms318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318 PELComplexPeriodSurface318
open PELJointArithmeticLift318 PELPrincipalThreeFreeAction318 PELPrincipalProperAction318
open PELPrincipalThreeCovering318 PELJointHolomorphicLift318
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000

/-- Original left-order endomorphism on the actual JOINT family. -/
@[expose] def jointOrder (a : order) (p : Total) : Total :=
  (p.1,fiberEquiv p.1 (orderEnd representation order p.1 a ((fiberEquiv p.1).symm p.2)))
@[expose] def coverOrder (a : order) (p : Cover) : Cover :=
  (p.1,leftLinear (representation a) p.2)
@[expose] def ambientOrder (a : order) : Ambient →ₗ[ℂ] Ambient where
  toFun p := (p.1,leftLinear (representation a) p.2)
  map_add' p q := Prod.ext rfl (map_add _ _ _)
  map_smul' c p := Prod.ext rfl (map_smul _ _ _)

theorem jointOrder_square (a : order) (p : Cover) :
    jointOrder a (familyProjection p)=familyProjection (coverOrder a p) := by
  rcases p with ⟨τ,z⟩
  rw [projection_fiber]
  change (τ,fiberEquiv τ (orderEnd representation order τ a
    ((fiberEquiv τ).symm (fiberEquiv τ (QuotientAddGroup.mk' (Periods τ) z)))))=_
  rw [AddEquiv.symm_apply_apply,orderEnd_mk]
  exact (projection_fiber τ (leftLinear (representation a) z)).symm

theorem coverOrder_ambient (a : order) (p : Cover) :
    ambient (coverOrder a p)=ambientOrder a (ambient p) := rfl

local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

/-- Holomorphy is JOINT in parameter and surface point, not merely a
separate endomorphism theorem on each compact fiber. -/
theorem jointOrder_holomorphic (a : order) :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (jointOrder a) :=
  joint_map_holomorphic (jointOrder a) (coverOrder a) (ambientOrder a)
    (jointOrder_square a) (coverOrder_ambient a)
    (fun _ _ => (ambientOrder a).toContinuousLinearMap.contDiff.contDiffAt)

/-- Original left order multiplication commutes with right-unit arithmetic
transport, retaining the actual automorphy scalar on all covering vectors. -/
theorem coverOrder_commutes (a : order) (u : principalThree) (p : Cover) :
    coverOrder a (lift u.val (determinant u) p)=
      lift u.val (determinant u) (coverOrder a p) := by
  simp only [coverOrder,lift]
  exact Prod.ext rfl (map_smul (leftLinear (representation a)) _ _)

theorem jointOrder_commutes (a : order) (u : principalThree) (p : Total) :
    jointOrder a (u • p)=u • jointOrder a p := by
  obtain ⟨x,rfl⟩ := familyProjection_surjective p
  calc
    _ = jointOrder a (familyProjection (lift u.val (determinant u) x)) :=
      congrArg (jointOrder a) (PELPrincipalThreeFreeAction318.projection_square u x)
    _ = familyProjection (coverOrder a (lift u.val (determinant u) x)) := jointOrder_square a _
    _ = familyProjection (lift u.val (determinant u) (coverOrder a x)) :=
      congrArg familyProjection (coverOrder_commutes a u x)
    _ = u • familyProjection (coverOrder a x) :=
      (PELPrincipalThreeFreeAction318.projection_square u _).symm
    _ = u • jointOrder a (familyProjection x) := congrArg (fun p => u • p) (jointOrder_square a x).symm

theorem jointOrder_over_base (a : order) (p : Total) : (jointOrder a p).1=p.1 := rfl

/-- Every original fiber's endomorphism is exactly the one consumed by
the joint construction, with no change to its original quotient lattice. -/
theorem jointOrder_original_fiber (a : order) (τ : HalfPlane) (p : Surface τ) :
    jointOrder a (τ,fiberEquiv τ p)=(τ,fiberEquiv τ (orderEnd representation order τ a p)) := by
  change (τ,fiberEquiv τ (orderEnd representation order τ a ((fiberEquiv τ).symm (fiberEquiv τ p))))=_
  rw [AddEquiv.symm_apply_apply]
end PELJointOrderEndomorphisms318
