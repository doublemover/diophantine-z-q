module
public import ActualTwoDescentOriginalThreeSquareCompatibility318
public import ModuleLocalIsomorphism318
public section
noncomputable section
namespace ActualTwoDescentOpenChartAmbientCoordinates318
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

lemma image_preimage (V : X.Opens) (hV : V≤j.opensRange) : j ''ᵁ (j⁻¹ᵁ V)=V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,inf_eq_right.mpr hV]

/-- Exact original section-ring isomorphism on any ambient subopen of
the chart image. This is not a new choice of chart coordinates. -/
def ambientRingIso (V : X.Opens) (hV : V≤j.opensRange) : Γ(X,V) ≅ Γ(Y,j⁻¹ᵁ V) :=
  X.presheaf.mapIso (eqToIso (image_preimage j V hV)).op ≪≫ j.appIso (j⁻¹ᵁ V)

lemma ambientRingIso_hom (V : X.Opens) (hV : V≤j.opensRange) :
    (ambientRingIso j V hV).hom=j.app V := by
  change X.presheaf.map (eqToHom (image_preimage j V hV)).op ≫
    (j.appIso (j⁻¹ᵁ V)).hom=j.app V
  have he : X.presheaf.map (eqToHom (image_preimage j V hV)).op=
      X.presheaf.map (homOfLE (j.image_preimage_le V)).op := rfl
  rw [he,←j.app_appIso_inv V]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

abbrev adjoint (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf) :=
  (Scheme.Modules.restrictAdjunction j).homEquiv _ _ f

/-- The native adjoint produces the actual chart value. Inverting the
actual structure-ring map returns a linear map over the ORIGINAL ambient
section ring,which can be consumed by ModuleLocalGluing. -/
def coordinate (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (V : X.Opens) (hV : V≤j.opensRange) : Γ(M,V) →ₗ[Γ(X,V)] Γ(X,V) where
  toFun s := (ambientRingIso j V hV).inv ((adjoint j M f).app V s)
  map_add' s t := by rw [map_add,map_add]
  map_smul' a s := by
    have hh := Scheme.Modules.Hom.app_smul (adjoint j M f) a s
    change (adjoint j M f).app V (a • s)=j.app V a*(adjoint j M f).app V s at hh
    rw [hh,map_mul,←ambientRingIso_hom j V hV]
    change (ambientRingIso j V hV).inv ((ambientRingIso j V hV).hom a)*_=_
    rw [←CommRingCat.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] <;> rfl

lemma coordinate_structure (M : X.Modules)
    (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (V : X.Opens) (hV : V≤j.opensRange) (s : Γ(M,V)) :
    j.app V (coordinate j M f V hV s)=(adjoint j M f).app V s := by
  rw [←ambientRingIso_hom j V hV]
  change (ambientRingIso j V hV).hom ((ambientRingIso j V hV).inv _)=_
  rw [←CommRingCat.comp_apply,Iso.inv_hom_id,ConcreteCategory.id_apply]
end ActualTwoDescentOpenChartAmbientCoordinates318
