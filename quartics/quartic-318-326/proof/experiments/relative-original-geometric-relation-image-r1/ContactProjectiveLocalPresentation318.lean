module
public import ContactQuotientOriginalBaseChange318
public import AffineCoefficientOverlapTests318
public section
noncomputable section
namespace ContactProjectiveLocalPresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q]
/-- A genuine whole coefficient cover with local original quotient
presentations of the SAME closed projective family. Cartesian source
squares, not assumed classifying-map agreement, are the input. -/
structure Data where
  coefficients : AffineCoefficientCover318.Data ℚ S
  chart : coefficients.Index → Chart
  ideal : ∀ i, Ideal c (chart i) (coefficients.ring i) n
  toFamily : ∀ i, family c (chart i) (coefficients.ring i) n (ideal i) ⟶ Z
  cartesian : ∀ i, IsPullback (toFamily i)
    (projectiveInto c (chart i) (coefficients.ring i) n (ideal i)) q
    (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S (coefficients.ring i)
      (coefficients.coefficient i) (ContactIntrinsicDifferentials318.structureMap c))
variable (D : Data c n S q)
@[expose] def localPoint (i : D.coefficients.Index) : ContactProjectiveParameterPoint318.Point c n (D.coefficients.ring i) :=
  ContactProjectiveParameterPoint318.ofIdeal c n (D.coefficients.ring i) (D.chart i) (D.ideal i)
end ContactProjectiveLocalPresentation318
