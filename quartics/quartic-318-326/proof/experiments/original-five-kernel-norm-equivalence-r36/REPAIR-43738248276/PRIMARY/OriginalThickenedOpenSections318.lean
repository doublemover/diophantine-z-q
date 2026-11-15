module
public import OriginalReducedFrameCocycle318
public section
noncomputable section
namespace OriginalThickenedOpenSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 OriginalThickenedOpen318
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Transport the map and its dependent open-inclusion proof together. -/
private lemma appLE_of_eq {Y Z : Scheme.{u}} (f g : Y ⟶ Z) (h : f = g)
    (U : Z.Opens) (V : Y.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R) (V : X.Opens)
abbrev π := pullback.fst p (structureMap R)
lemma inclusion_preimage : (⊤ : (Local R p V).Opens) ≤ inclusion R p V ⁻¹ᵁ (π R p ⁻¹ᵁ V) := by
  rw [← image R p V, Scheme.Hom.preimage_image_eq]
@[expose] def baseIso : Γ(X,V) ≅ Γ(V.toScheme,⊤) :=
  X.presheaf.mapIso (eqToIso (Scheme.Opens.ι_image_top V)).op ≪≫ V.ι.appIso ⊤
@[expose] def sectionsIso : Γ(thickening R p,π R p ⁻¹ᵁ V) ≅ Γ(Local R p V,⊤) :=
  (thickening R p).presheaf.mapIso (eqToIso (image R p V)).op ≪≫ (inclusion R p V).appIso ⊤
lemma baseIso_hom : (baseIso V).hom = V.ι.appLE V ⊤ (by simp) := by
  simp [baseIso, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  apply congrArg X.presheaf.map
  exact Subsingleton.elim _ _
lemma sectionsIso_hom : (sectionsIso R p V).hom =
    (inclusion R p V).appLE (π R p ⁻¹ᵁ V) ⊤ (inclusion_preimage R p V) := by
  simp [sectionsIso, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
lemma coefficient_square : (π R p).app V ≫ (sectionsIso R p V).hom =
    (baseIso V).hom ≫ (π R (localBase R p V)).appTop := by
  rw [sectionsIso_hom, baseIso_hom]
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_of_eq _ _ (inclusion_fst R p V) _ _ _ _
lemma reduction_preimage : reduction R p ⁻¹ᵁ (π R p ⁻¹ᵁ V) = V := by
  rw [← Scheme.Hom.comp_preimage, reduction_fst]
  all_goals rfl
@[expose] def reduce : Γ(thickening R p,π R p ⁻¹ᵁ V) ⟶ Γ(X,V) :=
  (reduction R p).appLE (π R p ⁻¹ᵁ V) V (le_of_eq (reduction_preimage R p V).symm)
lemma reduction_square : (sectionsIso R p V).hom ≫ (reduction R (localBase R p V)).appTop =
    reduce R p V ≫ (baseIso V).hom := by
  rw [sectionsIso_hom, baseIso_hom]
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]
  dsimp only [reduce]
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_of_eq _ _ (reduction_map R (localBase R p V) p V.ι rfl) _ _ _ _
/-- The ORIGINAL epsilon section on the entire inverse-image open is carried
to the original epsilon of the actual local thickening. -/
lemma epsilon_square : (sectionsIso R p V).hom
    (InfinitesimalUnitCocycle318.epsilon (thickening R p)
      (DualNumberInfinitesimalLines318.epsilon R p) (π R p ⁻¹ᵁ V)) =
        DualNumberInfinitesimalLines318.epsilon R (localBase R p V) := by
  rw [sectionsIso_hom]
  change ((thickening R p).presheaf.map (homOfLE (show π R p ⁻¹ᵁ V ≤ ⊤ from le_top)).op ≫
    (inclusion R p V).appLE (π R p ⁻¹ᵁ V) ⊤ (inclusion_preimage R p V))
      (DualNumberInfinitesimalLines318.epsilon R p) = _
  rw [Scheme.Hom.map_appLE]
  simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top, inclusion] using
    DualNumberCocycleNaturality318.epsilon_naturality (R := R) (localBase R p V) p V.ι rfl
end OriginalThickenedOpenSections318
