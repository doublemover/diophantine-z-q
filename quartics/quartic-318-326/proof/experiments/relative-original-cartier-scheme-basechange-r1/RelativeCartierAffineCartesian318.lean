module
public import RelativeCartierAffineBaseChange318
public import RegularClosedSquareIso318
public section
noncomputable section
namespace RelativeCartierAffineCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]
  {Z X W Y : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ Spec R) [hflat : Flat (p ≫ a)]
  (q : W ⟶ Y) (t : W ⟶ Z) (g : Y ⟶ X) (b : Y ⟶ Spec S)
  (F : IsPullback t q p g)
  (K : IsPullback g b a (RelativeOriginalAffineChart318.baseMap R S))
local notation "f" => RelativeOriginalAffineChart318.baseMap R S
local notation "P" => ClosedFamilyBaseRestriction318.into a p f
@[expose] def familyIso : W ≅ ClosedFamilyBaseRestriction318.family a p f :=
  (F.paste_vert K).isoPullback
@[reassoc] lemma familyIso_source : (familyIso R S p a q t g b F K).hom ≫ P=q ≫ K.isoPullback.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc,ClosedFamilyBaseRestriction318.into_fst,← Category.assoc,
      IsPullback.isoPullback_hom_fst,Category.assoc,IsPullback.isoPullback_hom_fst]
    exact F.w
  · rw [Category.assoc,ClosedFamilyBaseRestriction318.into_snd,
      IsPullback.isoPullback_hom_snd,Category.assoc,IsPullback.isoPullback_hom_snd]
include F K hflat in
/-- Cartier stability is independent of the chosen actual pullback
model: both the entire closed-family and ambient Cartesian squares are
retained, rather than identifying only affine points or supports. -/
lemma regular (h : OriginalRegularClosedCharts318.Property p) :
    OriginalRegularClosedCharts318.Property q := by
  have he : (familyIso R S p a q t g b F K).inv ≫ q=P ≫ K.isoPullback.inv := by
    apply (cancel_mono K.isoPullback.hom).mp
    rw [Category.assoc,← familyIso_source,← Category.assoc,Iso.inv_hom_id_assoc,
      Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact RegularClosedSquareIso318.transport P q (familyIso R S p a q t g b F K).symm
    K.isoPullback.symm he (RelativeCartierAffineBaseChange318.regular R S p a h)
end RelativeCartierAffineCartesian318
