module
public import IntrinsicOpenRestriction318
public import AffineIntrinsicFrames318
public section
noncomputable section
namespace FamilyOpenRestriction318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  {R : CommRingCat.{u}}

theorem coefficients_global (c : R ⟶ Γ(Y,⊤)) :
    DerivationOpenRestriction318.coefficients j
      (FamilyIntrinsicDifferentials318.coefficientPresheaf R c) =
        FamilyIntrinsicDifferentials318.coefficientPresheaf R (c ≫ j.appTop) := by
  apply NatTrans.ext
  funext U
  change (c ≫ Y.presheaf.map (homOfLE le_top).op) ≫ (j.appIso U.unop).hom =
    (c ≫ j.appTop) ≫ X.presheaf.map (homOfLE le_top).op
  rw [Category.assoc,Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE]
  rfl

theorem coefficients_comp (p : Y ⟶ Spec R) :
    DerivationOpenRestriction318.coefficients j (FamilyIntrinsicDifferentials318.coefficients p) =
      FamilyIntrinsicDifferentials318.coefficients (j ≫ p) := by
  unfold FamilyIntrinsicDifferentials318.coefficients
  rw [coefficients_global,Scheme.Hom.comp_appTop,Category.assoc]

/-- Intrinsic relative Omega for a scheme over Spec R commutes with restriction
through the exact actual composite structure map. -/
@[expose] def restrictIso (p : Y ⟶ Spec R) :
    (FamilyIntrinsicDifferentials318.omega p).restrict j ≅
      FamilyIntrinsicDifferentials318.omega (j ≫ p) :=
  (IntrinsicOpenRestriction318.iso j (FamilyIntrinsicDifferentials318.coefficients p)).symm ≪≫
    eqToIso (by unfold FamilyIntrinsicDifferentials318.omega; rw [coefficients_comp])

/-- The same comparison expressed with the actual Scheme.Modules pullback. -/
@[expose] def pullbackIso (p : Y ⟶ Spec R) :
    (Scheme.Modules.pullback j).obj (FamilyIntrinsicDifferentials318.omega p) ≅
      FamilyIntrinsicDifferentials318.omega (j ≫ p) :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm ≪≫ restrictIso j p

/-- On an affine open chart with its exact structural map, the restriction of
intrinsic global Omega is the genuine tilde algebraic Kähler sheaf. -/
@[expose] def affineChartIso {S : CommRingCat.{u}} (j : Spec S ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec R) (f : R ⟶ S) (h : j ≫ p=Spec.map f) :
    (FamilyIntrinsicDifferentials318.omega p).restrict j ≅
      tilde (CommRingCat.KaehlerDifferential f) :=
  restrictIso j p ≪≫ eqToIso (congrArg FamilyIntrinsicDifferentials318.omega h) ≪≫
    (AffineIntrinsicFrames318.specMapIso f).symm
end FamilyOpenRestriction318
