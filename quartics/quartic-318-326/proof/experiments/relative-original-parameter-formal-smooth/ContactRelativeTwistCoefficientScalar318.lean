module
public import ContactRelativeTwistPowers318
public import ContactCoefficientWholeOpens318
public import OriginalFunctionTransport318
public section
noncomputable section
namespace ContactRelativeTwistCoefficientScalar318
open AlgebraicGeometry CategoryTheory
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactRelativeWholeOpenSections318 ContactRelativeCoefficientChange318
open ContactRelativeGeometricTwist318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ)
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- The original coefficient map preserves EVERY Laurent monomial in the
same full overlap ring, including negative powers. -/
lemma ring_monomial (d : ℤ) : overlapRingMap R S f c
    (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (LaurentPolynomial.T d)) =
      ContactOriginalRelativeOverlapCoordinates318.laurentMap S c (LaurentPolynomial.T d) := by
  rw [RelativeOriginalLaurentAlgebra318.laurentMap_T,
    RelativeCoefficientChange318.ringMap_tmul,map_one,
    RelativeOriginalLaurentAlgebra318.laurentMap_T]

/-- Equality of the original actual ambient regular functions on the full
intersection, not just of their affine coordinate representatives. -/
lemma ambient_monomial (d : ℤ) :
    OriginalFunctionTransport318.pullTo (curveMap R S f c)
      (finiteOpen R c ⊓ infinityOpen R c) (finiteOpen S c ⊓ infinityOpen S c)
      (ContactCoefficientWholeOpens318.overlap_preimage R S f c)
      (scalar R c (LaurentPolynomial.T d)) = scalar S c (LaurentPolynomial.T d) := by
  change OriginalFunctionTransport318.pullTo _ _ _ _
    (OriginalFunctionTransport318.chartScalar (into R c) _ (overlap_image R c)
      (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (LaurentPolynomial.T d))) = _
  rw [OriginalFunctionTransport318.chart_square (overlapRingMap R S f c)
    (curveMap R S f c) (into S c) (into R c) (overlap_square R S f c).symm
    _ _ (overlap_image R c) (overlap_image S c)
    (ContactCoefficientWholeOpens318.overlap_preimage R S f c),ring_monomial]
  rfl

lemma transition (d : ℤ) :
    Units.map (OriginalFunctionTransport318.pullTo (curveMap R S f c)
      (finiteOpen R c ⊓ infinityOpen R c) (finiteOpen S c ⊓ infinityOpen S c)
      (ContactCoefficientWholeOpens318.overlap_preimage R S f c)).toMonoidHom
      (ContactRelativeGeometricTwist318.transition R c d) =
      ContactRelativeGeometricTwist318.transition S c d := by
  apply Units.ext
  exact ambient_monomial R S f c d
end ContactRelativeTwistCoefficientScalar318
