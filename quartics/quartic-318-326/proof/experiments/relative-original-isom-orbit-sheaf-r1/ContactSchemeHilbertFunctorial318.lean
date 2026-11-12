module
public import ContactSchemeHilbertNaturality318
public section
noncomputable section
namespace ContactSchemeHilbertFunctorial318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B T U : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (u : U ⟶ Spec (CommRingCat.of ℚ)) (D : ContactSchemeHilbertData318.Data c n b)
lemma source_id : RelativeSchemeCoefficient318.map (ContactIntrinsicDifferentials318.structureMap c)
    b b (𝟙 B) (Category.id_comp b)=𝟙 _ := by
  apply pullback.hom_ext
  · rw [RelativeSchemeCoefficient318.map_fst,Category.id_comp]
  · rw [RelativeSchemeCoefficient318.map_snd,Category.comp_id,Category.id_comp]
lemma map_id : ContactSchemeHilbertBaseChange318.map c n b b (𝟙 B) (Category.id_comp b) D=D := by
  apply ContactSchemeHilbertData318.Data.ext
  change D.ideal.comap (RelativeSchemeCoefficient318.map _ b b (𝟙 B) (Category.id_comp b))=D.ideal
  rw [source_id,Scheme.IdealSheafData.comap_id]
lemma map_comp (g : T ⟶ B) (hg : g ≫ b=t) (h : U ⟶ T) (hh : h ≫ t=u) :
    ContactSchemeHilbertBaseChange318.map c n t u h hh
      (ContactSchemeHilbertBaseChange318.map c n b t g hg D)=
      ContactSchemeHilbertBaseChange318.map c n b u (h ≫ g) (by rw [Category.assoc,hg]; exact hh) D := by
  apply ContactSchemeHilbertData318.Data.ext
  change (D.ideal.comap (RelativeSchemeCoefficient318.map _ b t g hg)).comap
    (RelativeSchemeCoefficient318.map _ t u h hh)=_
  rw [← Scheme.IdealSheafData.comap_comp,RelativeSchemeCoefficient318.comp]
end ContactSchemeHilbertFunctorial318
