module
public import IntrinsicTensorSheaf318
public import Mathlib.CategoryTheory.Sites.CoverLifting
public section
noncomputable section
namespace OpenSheafification318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

@[expose] def sheafify {X : Scheme.{u}} (P : X.PresheafOfModules) : X.Modules :=
  (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P

@[expose] def unit {X : Scheme.{u}} (P : X.PresheafOfModules) : P ⟶ (sheafify P).val :=
  PresheafOfModules.sheafificationHomEquiv (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) (𝟙 _)

theorem unit_underlying {X : Scheme.{u}} (P : X.PresheafOfModules) :
    (PresheafOfModules.toPresheaf _).map (unit P)=
      CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
  rw [unit,PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  change CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf ≫ 𝟙 _ = _
  exact Category.comp_id _

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

@[expose] def coefficients : X.ringCatSheaf.obj ⟶ j.opensFunctor.op ⋙ Y.ringCatSheaf.obj :=
  Functor.whiskerRight
    (show X.presheaf ⟶ j.opensFunctor.op ⋙ Y.presheaf from
      { app U := (j.appIso U.unop).inv
        naturality {U V} i := j.appIso_inv_naturality i }) (forget₂ CommRingCat RingCat)

@[expose] def restriction : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pushforward (coefficients j)

@[expose] def comparison (P : Y.PresheafOfModules) :
    sheafify ((restriction j).obj P) ⟶ (sheafify P).restrict j :=
  (PresheafOfModules.sheafificationHomEquiv (R:=X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).symm ((restriction j).map (unit P))

theorem comparison_underlying (P : Y.PresheafOfModules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (comparison j P) =
      (j.opensFunctor.pushforwardContinuousSheafificationCompatibility AddCommGrpCat
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).hom.app P.presheaf := by
  apply ((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
    AddCommGrpCat).homEquiv _ _).injective
  rw [←PresheafOfModules.toPresheaf_map_sheafificationHomEquiv]
  rw [comparison,Equiv.apply_symm_apply]
  change Functor.whiskerLeft j.opensFunctor.op ((PresheafOfModules.toPresheaf _).map (unit P)) = _
  rw [unit_underlying]
  exact (j.opensFunctor.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) P.presheaf).symm

instance comparison_isIso (P : Y.PresheafOfModules) : IsIso (comparison j P) := by
  have h : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map (comparison j P)) := by
    rw [comparison_underlying]
    infer_instance
  letI := h
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact (inferInstance : IsIso (((SheafOfModules.toSheaf X.ringCatSheaf).map (comparison j P)).hom.app (op U)))

@[expose] def iso (P : Y.PresheafOfModules) :
    sheafify ((restriction j).obj P) ≅ (sheafify P).restrict j := asIso (comparison j P)
end OpenSheafification318
