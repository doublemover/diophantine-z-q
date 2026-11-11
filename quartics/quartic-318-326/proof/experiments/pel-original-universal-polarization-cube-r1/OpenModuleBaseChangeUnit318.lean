module
public import OpenModuleCartesianBaseChange318
public import IntegralOpenUnitMonomorphism318
public section
noncomputable section
namespace OpenModuleBaseChangeUnit318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OpenCartesianSectionSquare318 OpenModuleCartesianBaseChange318
open IntegralOpenUnitMonomorphism318
variable {W U V X : Scheme} (right : W ⟶ V) (left : W ⟶ U)
  (k : V ⟶ X) (j : U ⟶ X)
  [IsOpenImmersion right] [IsOpenImmersion left] [IsOpenImmersion k] [IsOpenImmersion j]
  (H : IsPullback right left k j)

/-- The canonical unit-sheaf specialization of genuine Cartesian base
change, followed by the actual restricted structure-module frame. -/
@[expose] def unitIso :
    (Scheme.Modules.restrictFunctor k).obj
      ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward right).obj (SheafOfModules.unit W.ringCatSheaf) :=
  objectIso right left k j H (SheafOfModules.unit U.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward right).mapIso (Scheme.Modules.restrictUnitIso left)

/-- Exact unit-map compatibility through the actual Cartesian square.
Both sides are morphisms of full module sheaves, not equality of selected
sections. It consumes the produced scalar square, not assumed base change. -/
theorem unit_square :
    (Scheme.Modules.restrictUnitIso k).inv≫
      (Scheme.Modules.restrictFunctor k).map (unitMap j)≫(unitIso right left k j H).hom=
    unitMap right := by
  apply Scheme.Modules.hom_ext
  intro O
  ext a
  change (left.appIso (right ⁻¹ᵁ O)).hom
      (U.presheaf.map (eqToHom (opens_square right left k j H O)).op
        ((unitMap j).app (k ''ᵁ O) ((k.appIso O).inv a)))=
    (unitMap right).app O a
  rw [unitMap_app,unitMap_app]
  have h := congrArg (fun f => f a) (scalar_square right left k j H O)
  change U.presheaf.map (eqToHom (opens_square right left k j H O)).op
    (j.app (k ''ᵁ O) ((k.appIso O).inv a))=
      (left.appIso (right ⁻¹ᵁ O)).inv (right.app O a) at h
  rw [h]
  exact Iso.inv_hom_id_apply _ _
end OpenModuleBaseChangeUnit318
