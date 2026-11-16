module
public import ContactFixedDegreeGlobalClassifier318
public import AffineCoefficientCoverSum318
public section
noncomputable section
namespace ContactProjectivePresentationSum318
open AlgebraicGeometry CategoryTheory
open ContactProjectiveLocalPresentation318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q]
  (D E : Data c n S q)
/-- Both arbitrary original quotient presentation systems enter one
actual whole cover of the SAME closed family. -/
@[expose] def sum : Data c n S q where
  coefficients := AffineCoefficientCoverSum318.sum ℚ S D.coefficients E.coefficients
  chart := Sum.elim D.chart E.chart
  ideal i := by cases i with | inl i => exact D.ideal i | inr j => exact E.ideal j
  toFamily i := by cases i with | inl i => exact D.toFamily i | inr j => exact E.toFamily j
  cartesian i := by cases i with | inl i => exact D.cartesian i | inr j => exact E.cartesian j
end ContactProjectivePresentationSum318
