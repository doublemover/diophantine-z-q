module
public import FamilyRestrictionNormalization318
public section
noncomputable section
namespace OpenChartSections318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y Z : Scheme.{u}} (k : Z ⟶ X) (j : X ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion j]

@[expose] def imageLE : (k ≫ j) ''ᵁ ⊤ ≤ j ''ᵁ ⊤ := by
  rw [Scheme.Hom.comp_image]
  exact j.image_mono le_top

/-- The actual global regular-function map between nested charts agrees with
restriction of ambient regular functions through both actual chart isomorphisms. -/
theorem restriction_square :
    (j.appIso ⊤).inv ≫ Y.presheaf.map (homOfLE (imageLE k j)).op ≫
      ((k ≫ j).appIso ⊤).hom = k.appTop := by
  rw [Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE]
  have h := Scheme.Hom.appLE_comp_appLE k j (j ''ᵁ ⊤) ⊤ ⊤
    (j.preimage_image_eq ⊤).ge (show (⊤ : Z.Opens) ≤ k ⁻¹ᵁ ⊤ from le_rfl)
  rw [←h]
  rw [←Scheme.Hom.appIso_hom']
  have hk : k.appLE ⊤ ⊤ (show (⊤ : Z.Opens) ≤ k ⁻¹ᵁ ⊤ from le_rfl) = k.appTop := by
    change k.appTop ≫ Z.presheaf.map (𝟙 (op ⊤)) = k.appTop
    exact (congrArg (fun m => k.appTop ≫ m) (Z.presheaf.map_id (op ⊤))).trans
      (Category.comp_id k.appTop)
  exact ((j.appIso ⊤).inv_hom_id_assoc _).trans hk

/-- The corresponding identity on actual ambient chart sections. -/
theorem restriction_apply (s : Γ(X,⊤)) :
    Y.presheaf.map (homOfLE (imageLE k j)).op ((j.appIso ⊤).inv s) =
      ((k ≫ j).appIso ⊤).inv (k.appTop s) := by
  have h := congrArg (fun f => f s) (restriction_square k j)
  have hi := congrArg ((k ≫ j).appIso ⊤).inv h
  exact (Iso.hom_inv_id_apply ((k ≫ j).appIso ⊤) _).symm.trans hi

variable {S T : CommRingCat.{u}}

theorem affine_restriction (f : S ⟶ T) [IsOpenImmersion (Spec.map f)]
    (j : Spec S ⟶ Y) [IsOpenImmersion j] (s : S) :
    Y.presheaf.map (homOfLE (imageLE (Spec.map f) j)).op
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv s)) =
    ((Spec.map f ≫ j).appIso ⊤).inv ((Scheme.ΓSpecIso T).inv (f s)) := by
  have h := restriction_apply (Spec.map f) j ((Scheme.ΓSpecIso S).inv s)
  have hn := congrArg (fun k => k s) (Scheme.ΓSpecIso_inv_naturality f)
  exact h.trans (congrArg ((Spec.map f ≫ j).appIso ⊤).inv hn.symm)
end OpenChartSections318
