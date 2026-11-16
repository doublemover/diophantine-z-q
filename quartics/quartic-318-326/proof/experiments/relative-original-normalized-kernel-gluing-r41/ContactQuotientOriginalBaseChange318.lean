module
public import ContactProjectiveChartAgreement318
public import RelativeCoefficientFunctorial318
public section
noncomputable section
namespace ContactQuotientOriginalBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (a : Chart) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) (n : ℕ) (I : Ideal c a S n)
/-- The literal extended full quotient is the genuine base change in
the SAME whole original projective source, not only in its affine chart. -/
lemma cartesian : IsPullback (ContactQuotientChartCoefficient318.map c a S T φ n I)
    (projectiveInto c a T n (ContactQuotientChartCoefficient318.extended c a S T φ n I))
    (projectiveInto c a S n I)
    (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ (ContactIntrinsicDifferentials318.structureMap c)) := by
  apply IsPullback.of_bot
    (v₂₁ := ContactRelativeLinearOpenChart318.projection T c)
    (v₂₂ := ContactRelativeLinearOpenChart318.projection S c)
  · simpa only [ContactAffineQuotientToProjective318.into_projection] using
      ContactQuotientChartCoefficient318.cartesian c a S T φ n I
  · exact ContactQuotientChartCoefficient318.map_projective c a S T φ n I
  · exact RelativeCoefficientCartesian318.cartesian (CommRingCat.of ℚ) S T φ
      (ContactIntrinsicDifferentials318.structureMap c)
end ContactQuotientOriginalBaseChange318
