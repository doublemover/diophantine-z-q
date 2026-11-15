module
public import ContactProjectivePresentationSum318
public section
noncomputable section
namespace ContactProjectivePresentationIndependence318
open AlgebraicGeometry CategoryTheory
open ContactProjectiveLocalPresentation318 ContactProjectiveGlobalClassifyingMap318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q]
  (D E : Data c n S q)
local notation "DE" => ContactProjectivePresentationSum318.sum c n S q D E
lemma sum_left : point c n S q DE=point c n S q D := by
  apply Subtype.ext
  apply Scheme.Cover.hom_ext (AffineCoefficientCover318.cover ℚ S D.coefficients) _ _
  intro i
  exact (local_classify c n S q DE (Sum.inl i)).trans (local_classify c n S q D i).symm
lemma sum_right : point c n S q DE=point c n S q E := by
  apply Subtype.ext
  apply Scheme.Cover.hom_ext (AffineCoefficientCover318.cover ℚ S E.coefficients) _ _
  intro i
  exact (local_classify c n S q DE (Sum.inr i)).trans (local_classify c n S q E i).symm
/-- The ACTUAL global classifying morphism is independent of every
coefficient cover, source-chart choice and local quotient presentation. -/
lemma independent : point c n S q D=point c n S q E :=
  (sum_left c n S q D E).symm.trans (sum_right c n S q D E)
end ContactProjectivePresentationIndependence318
