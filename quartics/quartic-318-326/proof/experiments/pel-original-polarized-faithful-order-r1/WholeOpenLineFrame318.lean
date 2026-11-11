module
public import OpenLineFrameCoordinates318
public import ModuleGlobalSections318
public section
noncomputable section
namespace WholeOpenLineFrame318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules)
    (e : SheafOfModules.unit (⊤ : X.Opens).toScheme.ringCatSheaf ≅ M.restrict (⊤ : X.Opens).ι)
@[expose] def topSection : Γ(M,⊤) := OpenLineFrameCoordinates318.frame M ⊤ e ⊤ le_rfl 1
@[expose] def map : SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  ModuleGlobalSections318.ofTop M (topSection M e)
lemma map_apply (U : X.Opens) (a : Γ(X,U)) :
    (map M e).val.app (op U) a=OpenLineFrameCoordinates318.frame M ⊤ e U le_top a := by
  rw [map,ModuleGlobalSections318.ofTop_apply,topSection,
    OpenLineFrameCoordinates318.natural M ⊤ e le_rfl le_top,map_one]
  exact ((OpenLineFrameCoordinates318.frame M ⊤ e U le_top).map_smul a 1).symm.trans
    (by rw [smul_eq_mul,mul_one])
lemma map_isIso : IsIso (map M e) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h : (fun a : Γ(X,U) => (map M e).val.app (op U) a)=
      OpenLineFrameCoordinates318.frame M ⊤ e U le_top := funext (map_apply M e U)
  change Function.Bijective (fun a : Γ(X,U) => (map M e).val.app (op U) a)
  rw [h]
  exact (OpenLineFrameCoordinates318.frame M ⊤ e U le_top).bijective
/-- A genuine frame on the whole open yields a genuine global module
sheaf isomorphism; this is proved on EVERY open, not only top sections. -/
@[expose] def iso : SheafOfModules.unit X.ringCatSheaf ≅ M := by
  letI := map_isIso M e
  exact asIso (map M e)
end WholeOpenLineFrame318
