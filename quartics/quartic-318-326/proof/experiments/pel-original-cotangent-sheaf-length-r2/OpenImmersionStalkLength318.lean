module
public import CanonicalStalkModule318
public section
noncomputable section
namespace OpenImmersionStalkLength318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
/-- Direction is from the chart's local ring to the ambient local ring. -/
@[expose] def scalarIso (x : X) : X.presheaf.stalk x ≃+* Y.presheaf.stalk (j x) :=
  (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv
lemma stalkMap_germ_appIso (x : X) (U : X.Opens) (hx : x ∈ U) (r : Γ(X,U)) :
    j.stalkMap x (Y.presheaf.germ (j ''ᵁ U) (j x) (by simpa) ((j.appIso U).inv r)) =
      X.presheaf.germ U x hx r := by
  let i : U ⟶ j ⁻¹ᵁ (j ''ᵁ U) := eqToHom (j.preimage_image_eq U).symm
  have h : X.presheaf.map i.op (j.app (j ''ᵁ U) ((j.appIso U).inv r)) = r := by
    change ((j.app (j ''ᵁ U) ≫ X.presheaf.map i.op) ((j.appIso U).inv r)) = r
    rw [← Scheme.Hom.appIso_hom]
    exact Iso.inv_hom_id_apply (j.appIso U) r
  rw [j.germ_stalkMap_apply]
  exact (X.presheaf.germ_res_apply i x hx _).symm.trans
    (congrArg (X.presheaf.germ U x hx) h)
lemma scalarIso_germ (x : X) (U : X.Opens) (hx : x ∈ U) (r : Γ(X,U)) :
    scalarIso j x (X.presheaf.germ U x hx r) =
      Y.presheaf.germ (j ''ᵁ U) (j x) (by simpa) ((j.appIso U).inv r) := by
  apply (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).injective
  rw [stalkMap_germ_appIso]
  exact Iso.inv_hom_id_apply (asIso (j.stalkMap x)) _
/-- Restriction commutes with actual stalks, and its actual additive
isomorphism is semilinear over the inverse structure-sheaf stalk map. -/
lemma map_smul (M : Y.Modules) (x : X) (r : X.presheaf.stalk x)
    (m : CanonicalStalkModule318.stalk (M.restrict j) x) :
    (Scheme.Modules.restrictStalkNatIso j x).hom.app M (r • m) =
      scalarIso j x r • (Scheme.Modules.restrictStalkNatIso j x).hom.app M m := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, s, rfl⟩ := (M.restrict j).presheaf.exists_le_germ_eq m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a,
    ← PresheafOfModules.germ_smul (M.restrict j).val x V hxV,
    scalarIso_germ j x V hxV]
  have hg (t : Γ(M.restrict j,V)) :
      (Scheme.Modules.restrictStalkNatIso j x).hom.app M
        ((M.restrict j).presheaf.germ V x hxV t) =
      M.presheaf.germ (j ''ᵁ V) (j x) (by simpa) t :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x M hxV) t
  rw [hg, hg]
  change M.presheaf.germ (j ''ᵁ V) (j x) _ (((j.appIso V).inv _) • s) = _
  exact PresheafOfModules.germ_smul M.val (j x) (j ''ᵁ V) _ _ s
@[expose] def iso (M : Y.Modules) (x : X) :
    CanonicalStalkModule318.stalk (M.restrict j) x ≃ₛₗ[(scalarIso j x).toRingHom]
      CanonicalStalkModule318.stalk M (j x) where
  __ := ((Scheme.Modules.restrictStalkNatIso j x).app M).addCommGroupIsoToAddEquiv
  map_smul' := map_smul j M x
/-- Equality of lengths over the two genuine local rings. -/
theorem length_eq (M : Y.Modules) (x : X) :
    Module.length (X.presheaf.stalk x) (CanonicalStalkModule318.stalk (M.restrict j) x) =
      Module.length (Y.presheaf.stalk (j x)) (CanonicalStalkModule318.stalk M (j x)) :=
  CanonicalStalkModule318.length_semilinear (scalarIso j x) (iso j M x)
end OpenImmersionStalkLength318
