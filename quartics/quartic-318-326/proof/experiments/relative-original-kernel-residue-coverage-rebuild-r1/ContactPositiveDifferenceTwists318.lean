module
public import ContactNormalizedPairDifference318
public section
noncomputable section
namespace ContactPositiveDifferenceTwists318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeGeometricTwist318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
abbrev unitLine := LineSheafUnit318.line (curve R c)
abbrev numerator (n : ℕ) := twist R c L (n:ℤ)
abbrev denominator (n : ℕ) := twist R c (unitLine R c) (n:ℤ)
/-- Two SAME positive twists cancel literally in original line classes.
The second line is not an assumed effective representative: its genuine
normalized Cartier family is constructed separately. -/
lemma class_difference (n : ℕ) : classOf (numerator R c L n)*(classOf (denominator R c n))⁻¹=classOf L := by
  rw [ContactPositiveAbelPresentation318.twist_class,ContactPositiveAbelPresentation318.twist_class]
  have hu : classOf (unitLine R c)=(1 : Class (curve R c)) := rfl
  rw [hu,one_mul,mul_inv_cancel_right]
end ContactPositiveDifferenceTwists318
