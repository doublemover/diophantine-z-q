module
public import IntrinsicOpenRestriction318
public section
noncomputable section
namespace OpenDifferentialNaturality318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  {R : CommRingCat.{u}} (φ : (Functor.const Y.Opensᵒᵖ).obj R ⟶ Y.presheaf)

/-- The intrinsic restriction isomorphism in the forward direction carries
literal restricted differentials to literal local differentials. -/
theorem restriction_D :
    (IntrinsicOpenRestriction318.D j φ).postcomp (IntrinsicOpenRestriction318.iso j φ).inv.val =
      UniversalSheafDifferentials318.D (DerivationOpenRestriction318.coefficients j φ) := by
  rw [←IntrinsicOpenRestriction318.iso_D j φ,UniversalSheafDifferentials318.postcomp_comp]
  have h : (IntrinsicOpenRestriction318.iso j φ).hom.val ≫
      (IntrinsicOpenRestriction318.iso j φ).inv.val = 𝟙 _ := by
    exact congrArg (fun f => f.val) (IntrinsicOpenRestriction318.iso j φ).hom_inv_id
  rw [h]
  rfl

theorem restriction_D_apply (U : X.Opens) (s : Γ(X,U)) :
    (IntrinsicOpenRestriction318.iso j φ).inv.val.app (op U)
      ((UniversalSheafDifferentials318.D φ).d ((j.appIso U).inv s)) =
    (UniversalSheafDifferentials318.D (DerivationOpenRestriction318.coefficients j φ)).d s :=
  PresheafOfModulesOfCommRing.Derivation.congr_d (restriction_D j φ) s
end OpenDifferentialNaturality318
