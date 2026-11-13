module
public import ContactUniversalOriginalIsom318
public section
noncomputable section
namespace OriginalNativeIsomPullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
  (h : f ≫ g=k) (L K M : Line Z)
/-- The already native-defined coefficient-path pullback preserves the
identity on the SAME original pulled module. -/
lemma identity :
    OriginalPulledDifferencePath318.pullIso f g k h L L (Iso.refl _)=Iso.refl _ := by
  apply Iso.ext
  simp only [OriginalPulledDifferencePath318.pullIso,Iso.trans_hom,Iso.symm_hom,
    Iso.refl_hom,Functor.mapIso_hom,Functor.map_id,Category.id_comp,Iso.inv_hom_id]
lemma inverse
    (e : (LineSheafPullback318.line g L).object ≅ (LineSheafPullback318.line g K).object) :
    OriginalPulledDifferencePath318.pullIso f g k h K L e.symm=
      (OriginalPulledDifferencePath318.pullIso f g k h L K e).symm := by
  apply Iso.ext
  simp only [OriginalPulledDifferencePath318.pullIso,Iso.trans_hom,Iso.trans_inv,
    Iso.symm_hom,Iso.symm_inv,Functor.mapIso_hom,Functor.mapIso_inv,Category.assoc]
/-- Composition cancels the actual intermediate native associator; it
never identifies distinct original line objects by an unproved equality. -/
lemma composition
    (e : (LineSheafPullback318.line g L).object ≅ (LineSheafPullback318.line g K).object)
    (d : (LineSheafPullback318.line g K).object ≅ (LineSheafPullback318.line g M).object) :
    OriginalPulledDifferencePath318.pullIso f g k h L M (e ≪≫ d)=
      OriginalPulledDifferencePath318.pullIso f g k h L K e ≪≫
      OriginalPulledDifferencePath318.pullIso f g k h K M d := by
  apply Iso.ext
  simp only [OriginalPulledDifferencePath318.pullIso,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]
end OriginalNativeIsomPullback318
