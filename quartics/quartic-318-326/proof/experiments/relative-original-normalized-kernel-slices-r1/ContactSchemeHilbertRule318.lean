module
public import ContactSchemeHilbertTest318
public section
noncomputable section
namespace ContactSchemeHilbertRule318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactSchemeHilbertData318.Data c n b)
lemma test_natural (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T] (φ : S →ₐ[ℚ] T)
    (x : RelativeAffineTestRule318.Test ℚ b S) :
    ContactHilbertBaseChange318.map c n S T φ (ContactSchemeHilbertTest318.data c n b D S x)=
      ContactSchemeHilbertTest318.data c n b D T (RelativeAffineTestRule318.map ℚ b S T φ x) := by
  apply Subtype.ext
  apply ContactHilbertData318.Datum.ext
  change (D.ideal.comap (ContactSchemeHilbertTest318.sourceMap c b S x)).comap
    (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ
      (ContactIntrinsicDifferentials318.structureMap c))=
    D.ideal.comap (ContactSchemeHilbertTest318.sourceMap c b T (RelativeAffineTestRule318.map ℚ b S T φ x))
  rw [← Scheme.IdealSheafData.comap_comp,← OriginalAffineCoefficientIdentity318.map_eq,
    RelativeSchemeCoefficient318.comp]
  rfl
/-- Actual all-affine-test classification rule of an independently
specified standard original quotient over any coefficient scheme. -/
@[expose] def rule : RelativeAffineTestRule318.Rule ℚ b (ContactProjectiveParameterStructure318.structureMap c n) where
  app S _ x := ContactHilbertFixedRankEquiv318.equivalence c n S (ContactSchemeHilbertTest318.data c n b D S x)
  natural S T _ _ φ x := by
    rw [← test_natural]
    exact ContactHilbertBaseChange318.natural c n S T φ (ContactSchemeHilbertTest318.data c n b D S x)
@[expose] def classify : B ⟶ ContactProjectiveQuotientParameter318.scheme c n :=
  RelativeAffineTestGluing318.realize ℚ b (ContactProjectiveParameterStructure318.structureMap c n) (rule c n b D)
@[reassoc] lemma over : classify c n b D ≫ ContactProjectiveParameterStructure318.structureMap c n=b :=
  RelativeAffineTestGluing318.over ℚ _ _ _
@[reassoc] lemma evaluate (S : CommRingCat.{0}) [Algebra ℚ S] (x : RelativeAffineTestRule318.Test ℚ b S) :
    x.val ≫ classify c n b D=
      (ContactHilbertFixedRankEquiv318.equivalence c n S (ContactSchemeHilbertTest318.data c n b D S x)).val :=
  RelativeAffineTestEvaluation318.evaluate ℚ _ _ _ S x
end ContactSchemeHilbertRule318
