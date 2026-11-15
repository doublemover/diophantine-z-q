module
public import SectionZeroPullbackCover318
public section
noncomputable section
namespace SectionZeroPullbackChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open SectionZeroAffineRefinement318 OriginalSectionPullbackComposition318
universe u
variable {Z X W Y : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ Y)
  (t : W ⟶ Z) (g : Y ⟶ X) (F : IsPullback t q p g)
  (L : Line X) (s : Γ(L.object,⊤)) (D : SectionZeroChartData318.Data p L s)
  (i : SectionZeroPullbackCover318.index p L s D g)
local notation "A" => D.ring i.1
local notation "B" => SectionZeroPullbackCover318.ring p L s D g i
local notation "j" => D.into i.1
local notation "k" => SectionZeroPullbackCover318.into p L s D g i
local notation "φ" => SectionZeroPullbackCover318.ringMap p L s D g i
local notation "I" => sectionIdeal A j L s
local notation "J" => sectionIdeal B k (LineSheafPullback318.line g L) (pull g L.object s)
lemma ideal : I.map φ.hom=J :=
  (SectionZeroSquareIdeal318.ideal g A B φ j k (SectionZeroPullbackCover318.square p L s D g i) L s).symm
@[expose] def original : Spec (CommRingCat.of (B ⧸ J)) ⟶ Z :=
  Spec.map (AffineQuotientPushout318.arrow φ I J (ideal p g L s D i)) ≫ D.zero i.1
lemma outer : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (original p g L s D i) (k ≫ g) p := by
  rw [← SectionZeroPullbackCover318.square p L s D g i]
  exact (AffineQuotientPushout318.pullback φ I J (ideal p g L s D i)).paste_vert (D.cartesian i.1)
/-- The new section zero quotient maps into the SAME whole Cartesian
closed family; its full scheme structure is retained. -/
@[expose] def into : Spec (CommRingCat.of (B ⧸ J)) ⟶ W :=
  F.flip.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ k) (original p g L s D i)
    (by simpa only [Category.assoc] using (outer p g L s D i).w)
@[reassoc] lemma into_source : into p q t g F L s D i ≫ q=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ k := F.flip.lift_fst _ _ _
@[reassoc] lemma into_original : into p q t g F L s D i ≫ t=original p g L s D i := F.flip.lift_snd _ _ _
lemma cartesian : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (into p q t g F L s D i) k q := by
  apply IsPullback.of_bot (v₂₁ := g) (v₂₂ := p)
  · simpa only [into_original] using outer p g L s D i
  · exact (into_source p q t g F L s D i).symm
  · exact F.flip
end SectionZeroPullbackChart318
