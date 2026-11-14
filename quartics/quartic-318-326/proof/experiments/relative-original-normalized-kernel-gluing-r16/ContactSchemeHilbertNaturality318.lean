module
public import ContactSchemeHilbertBaseChange318
public section
noncomputable section
namespace ContactSchemeHilbertNaturality318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t) (D : ContactSchemeHilbertData318.Data c n b)
@[expose] def composeTest (S : CommRingCat.{0}) [Algebra ℚ S]
    (x : RelativeAffineTestRule318.Test ℚ t S) : RelativeAffineTestRule318.Test ℚ b S :=
  ⟨x.val ≫ g,by rw [Category.assoc,hg]; exact x.property⟩
lemma test_composition (S : CommRingCat.{0}) [Algebra ℚ S]
    (x : RelativeAffineTestRule318.Test ℚ t S) :
    ContactSchemeHilbertTest318.data c n t (ContactSchemeHilbertBaseChange318.map c n b t g hg D) S x=
      ContactSchemeHilbertTest318.data c n b D S (composeTest b t g hg S x) := by
  apply Subtype.ext
  apply ContactHilbertData318.Datum.ext
  change (D.ideal.comap (ContactSchemeHilbertBaseChange318.sourceMap c b t g hg)).comap
    (ContactSchemeHilbertTest318.sourceMap c t S x)=_
  rw [← Scheme.IdealSheafData.comap_comp,RelativeSchemeCoefficient318.comp]
  rfl
/-- Genuine naturality of the two-sided standard original Hilbert
classification under EVERY coefficient SCHEME morphism. -/
lemma natural : ContactSchemeHilbertEquiv318.equivalence c n t
    (ContactSchemeHilbertBaseChange318.map c n b t g hg D)=
      ContactSchemeHilbertBaseChange318.pointMap c n b t g hg
        (ContactSchemeHilbertEquiv318.equivalence c n b D) := by
  apply Subtype.ext
  apply RelativeAffineTestExt318.hom_ext ℚ t
  intro S _ x
  change x.val ≫ ContactSchemeHilbertRule318.classify c n t
      (ContactSchemeHilbertBaseChange318.map c n b t g hg D)=
    x.val ≫ (g ≫ ContactSchemeHilbertRule318.classify c n b D)
  rw [ContactSchemeHilbertRule318.evaluate,test_composition,← Category.assoc]
  exact (ContactSchemeHilbertRule318.evaluate c n b D S (composeTest b t g hg S x)).symm
end ContactSchemeHilbertNaturality318
