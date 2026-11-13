module
public import RelativeOriginalLaurentAlgebra318
public section
noncomputable section
namespace RelativeLaurentCoefficientTransport318
open LaurentPolynomial
open scoped TensorProduct AlgebraMonoidAlgebra
universe u
variable (k R B : Type u) [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra (LaurentPolynomial k) B]
  [IsScalarTower k (LaurentPolynomial k) B]

/-- The actual Laurent coefficient pushout preserves EVERY original
Laurent scalar, with the original ring inclusion on its right leg. -/
lemma original_scalar (l : LaurentPolynomial k) :
    RelativeOriginalLaurentAlgebra318.laurentMap k R B
      (algebraMap (LaurentPolynomial k) (LaurentPolynomial R) l) =
      (1 : R) ⊗ₜ[k] (algebraMap (LaurentPolynomial k) B l) :=
  RelativeOriginalLaurentAlgebra318.laurentMap_scalar k R B l
end RelativeLaurentCoefficientTransport318
