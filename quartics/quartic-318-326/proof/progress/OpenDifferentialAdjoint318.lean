module
public import OpenDifferentialNaturality318
public section
noncomputable section
namespace OpenDifferentialAdjoint318
open AlgebraicGeometry CategoryTheory
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  {R : CommRingCat.{u}} (φ : (Functor.const Y.Opensᵒᵖ).obj R ⟶ Y.presheaf)

theorem inverse_eq_desc :
    (IntrinsicOpenRestriction318.iso j φ).inv =
      IntrinsicOpenRestriction318.desc j φ
        (UniversalSheafDifferentials318.D (DerivationOpenRestriction318.coefficients j φ)) := by
  apply IntrinsicOpenRestriction318.hom_ext j φ
  exact (OpenDifferentialNaturality318.restriction_D j φ).trans
    (IntrinsicOpenRestriction318.desc_fac j φ _).symm

/-- The proved intrinsic restriction isomorphism has precisely the canonical
pushed universal-derivative map as its adjoint. -/
theorem restriction_adjoint :
    (Scheme.Modules.restrictAdjunction j).homEquiv _ _ (IntrinsicOpenRestriction318.iso j φ).inv =
      UniversalSheafDifferentials318.desc φ
        (DerivationOpenRestriction318.push j φ
          (UniversalSheafDifferentials318.D (DerivationOpenRestriction318.coefficients j φ))) := by
  rw [inverse_eq_desc]
  exact ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).apply_symm_apply _
end OpenDifferentialAdjoint318
