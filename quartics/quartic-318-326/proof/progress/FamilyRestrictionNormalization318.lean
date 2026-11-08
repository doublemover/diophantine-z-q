module
public import OpenDifferentialNaturality318
public import FamilyOpenRestriction318
public section
noncomputable section
namespace FamilyRestrictionNormalization318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  {R : CommRingCat.{u}}

structure Data (φ : (Functor.const Y.Opensᵒᵖ).obj R ⟶ Y.presheaf)
    (ψ : (Functor.const X.Opensᵒᵖ).obj R ⟶ X.presheaf) where
  iso : (UniversalSheafDifferentials318.omega φ).restrict j ≅
    UniversalSheafDifferentials318.omega ψ
  fac (U : X.Opens) (s : Γ(X,U)) : iso.hom.val.app (op U)
      ((UniversalSheafDifferentials318.D φ).d ((j.appIso U).inv s)) =
    (UniversalSheafDifferentials318.D ψ).d s

@[expose] def rawData (φ : (Functor.const Y.Opensᵒᵖ).obj R ⟶ Y.presheaf) :
    Data j φ (DerivationOpenRestriction318.coefficients j φ) :=
  ⟨(IntrinsicOpenRestriction318.iso j φ).symm,
    OpenDifferentialNaturality318.restriction_D_apply j φ⟩

@[expose] def familyData (p : Y ⟶ Spec R) :
    Data j (FamilyIntrinsicDifferentials318.coefficients p)
      (FamilyIntrinsicDifferentials318.coefficients (j ≫ p)) :=
  FamilyOpenRestriction318.coefficients_comp j p ▸ rawData j (FamilyIntrinsicDifferentials318.coefficients p)

@[expose] def iso (p : Y ⟶ Spec R) :
    (FamilyIntrinsicDifferentials318.omega p).restrict j ≅
      FamilyIntrinsicDifferentials318.omega (j ≫ p) := (familyData j p).iso

theorem restriction_D (p : Y ⟶ Spec R) (U : X.Opens) (s : Γ(X,U)) :
    (iso j p).hom.val.app (op U)
      ((FamilyIntrinsicDifferentials318.D p).d ((j.appIso U).inv s)) =
    (FamilyIntrinsicDifferentials318.D (j ≫ p)).d s :=
  (familyData j p).fac U s

/-- The adjoint of the intrinsic open comparison sends every actual ambient
differential to the derivative of its actual pullback regular function. -/
theorem adjoint_D (p : Y ⟶ Spec R) (U : Y.Opens) (s : Γ(Y,U)) :
    ((Scheme.Modules.restrictAdjunction j).homEquiv _ _ (iso j p).hom).val.app (op U)
      ((FamilyIntrinsicDifferentials318.D p).d s) =
    (FamilyIntrinsicDifferentials318.D (j ≫ p)).d (j.app U s) := by
  let V := j ⁻¹ᵁ U
  let i := (homOfLE (j.image_preimage_le U)).op
  have hj := congrArg (fun k => k s) (j.app_appIso_inv U)
  have hd := (FamilyIntrinsicDifferentials318.D p).d_map i s
  have ht := (congrArg (fun a => (FamilyIntrinsicDifferentials318.D p).d
    (X:=op (j ''ᵁ V)) a) hj).trans hd
  change (iso j p).hom.val.app (op V)
    ((FamilyIntrinsicDifferentials318.omega p).val.map i ((FamilyIntrinsicDifferentials318.D p).d s)) = _
  exact (congrArg ((iso j p).hom.val.app (op V)) ht).symm.trans
    (restriction_D j p V (j.app U s))
end FamilyRestrictionNormalization318
