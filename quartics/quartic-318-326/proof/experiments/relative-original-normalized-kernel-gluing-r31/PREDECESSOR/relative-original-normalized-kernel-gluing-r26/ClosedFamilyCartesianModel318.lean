module
public import RegularClosedBaseCover318
public section
noncomputable section
namespace ClosedFamilyCartesianModel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X W Y B T : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ B) (f : T ⟶ B) (q : W ⟶ Y) (t : W ⟶ Z) (g : Y ⟶ X) (b : Y ⟶ T)
  (F : IsPullback t q p g) (K : IsPullback g b a f)
local notation "P" => ClosedFamilyBaseRestriction318.into a p f
@[expose] def familyIso : W ≅ ClosedFamilyBaseRestriction318.family a p f :=
  (F.paste_vert K).isoPullback
@[reassoc] lemma familyIso_source : (familyIso p a f q t g b F K).hom ≫ P=q ≫ K.isoPullback.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc,ClosedFamilyBaseRestriction318.into_fst,← Category.assoc,
      IsPullback.isoPullback_hom_fst,Category.assoc,IsPullback.isoPullback_hom_fst]
    exact F.w
  · rw [Category.assoc,ClosedFamilyBaseRestriction318.into_snd,
      IsPullback.isoPullback_hom_snd,Category.assoc,IsPullback.isoPullback_hom_snd]
include F K in
/-- An actual Cartier result transports between two complete Cartesian
models of the SAME ambient and closed coefficient family. -/
lemma regular (h : OriginalRegularClosedCharts318.Property P) :
    OriginalRegularClosedCharts318.Property q := by
  have he : (familyIso p a f q t g b F K).inv ≫ q=P ≫ K.isoPullback.inv := by
    apply (cancel_mono K.isoPullback.hom).mp
    rw [Category.assoc,← familyIso_source,← Category.assoc,Iso.inv_hom_id_assoc,
      Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact RegularClosedSquareIso318.transport P q (familyIso p a f q t g b F K).symm
    K.isoPullback.symm he h
end ClosedFamilyCartesianModel318
