module
public import OpenChartSections318
public section
noncomputable section
namespace AffineChartPullbackScalars318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y X₀ Y₀ : Scheme.{u}} (f:X⟶Y) (j:X₀⟶X) [IsOpenImmersion j]
  (k:Y₀⟶Y) [IsOpenImmersion k] (g:X₀⟶Y₀) (h:j≫f=g≫k)

include h in
theorem image_le : j ''ᵁ ⊤ ≤ f ⁻¹ᵁ (k ''ᵁ ⊤) := by
  rintro _ ⟨x,_,rfl⟩
  exact ⟨g x,trivial,by exact congrArg (fun m=>m x) h.symm⟩

lemma appLE_congr_map {Z W:Scheme.{u}} {a b:Z⟶W} (e:a=b)
    (U:W.Opens) (V:Z.Opens) (ha:V≤a ⁻¹ᵁ U) (hb:V≤b ⁻¹ᵁ U) :
    a.appLE U V ha=b.appLE U V hb := by subst b; rfl

include h in
theorem map_square (hv:j ''ᵁ ⊤ ≤ f ⁻¹ᵁ (k ''ᵁ ⊤)) :
    f.appLE (k ''ᵁ ⊤) (j ''ᵁ ⊤) hv ≫ (j.appIso ⊤).hom =
      (k.appIso ⊤).hom ≫ g.appTop := by
  rw [Scheme.Hom.appIso_hom',Scheme.Hom.appLE_comp_appLE]
  have hg:(⊤:X₀.Opens)≤(g≫k) ⁻¹ᵁ (k ''ᵁ ⊤) := by
    rw [Scheme.Hom.comp_preimage,k.preimage_image_eq]
    exact le_rfl
  trans (g≫k).appLE (k ''ᵁ ⊤) ⊤ hg
  · exact appLE_congr_map h _ _ _ _
  · rw [←Scheme.Hom.appLE_comp_appLE g k (k ''ᵁ ⊤) ⊤ ⊤
      (k.preimage_image_eq ⊤).ge (show (⊤:X₀.Opens)≤g ⁻¹ᵁ ⊤ from le_rfl),
      ←Scheme.Hom.appIso_hom']
    congr 1
    change g.appTop ≫ X₀.presheaf.map (𝟙 (op ⊤))=g.appTop
    rw [X₀.presheaf.map_id,Category.comp_id]

variable {S T:CommRingCat.{u}} (a:S⟶T)

/-- Actual regular-function transport through an affine chart square. -/
theorem affine_scalar {X Y:Scheme.{u}} (f:X⟶Y)
    (j:Spec T⟶X) [IsOpenImmersion j] (k:Spec S⟶Y) [IsOpenImmersion k]
    (h:j≫f=Spec.map a≫k) (hv:j ''ᵁ ⊤ ≤ f ⁻¹ᵁ (k ''ᵁ ⊤)) (s:S) :
    f.appLE (k ''ᵁ ⊤) (j ''ᵁ ⊤) hv
      ((k.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv s)) =
        (j.appIso ⊤).inv ((Scheme.ΓSpecIso T).inv (a s)) := by
  apply (ConcreteCategory.bijective_of_isIso (j.appIso ⊤).hom).1
  have hh:=congrArg (fun m=>m ((k.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv s)))
    (map_square f j k (Spec.map a) h hv)
  have hn:=congrArg (fun m=>m s) (Scheme.ΓSpecIso_inv_naturality a)
  simp only [CommRingCat.comp_apply,Iso.inv_hom_id_apply] at hh ⊢
  exact hh.trans hn.symm
end AffineChartPullbackScalars318
