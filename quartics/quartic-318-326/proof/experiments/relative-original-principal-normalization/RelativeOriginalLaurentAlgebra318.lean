module
public import RelativeOriginalPolynomialAlgebra318
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace RelativeOriginalLaurentAlgebra318
open LaurentPolynomial
open scoped TensorProduct AlgebraMonoidAlgebra
universe u
variable (k R B : Type u) [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra (LaurentPolynomial k) B]
  [IsScalarTower k (LaurentPolynomial k) B]

/-- The canonical Laurent coefficient pushout uses all integer exponents,
including negative exponents, over an arbitrary coefficient ring. -/
def coefficientComparison : R ⊗[k] LaurentPolynomial k ≃ₐ[R] LaurentPolynomial R :=
  AddMonoidAlgebra.scalarTensorEquiv k R

/-- The actual Laurent-base-change presentation of the unchanged original
coefficient tensor ring. -/
def comparison : LaurentPolynomial R ⊗[LaurentPolynomial k] B ≃ₐ[R] R ⊗[k] B :=
  Algebra.IsPushout.cancelBaseChangeAlg k R (LaurentPolynomial k) (LaurentPolynomial R) B

lemma comparison_unit (b : B) : comparison k R B (1 ⊗ₜ[LaurentPolynomial k] b) =
    (1 : R) ⊗ₜ[k] b :=
  Algebra.IsPushout.cancelBaseChangeAlg_tmul k R (LaurentPolynomial k) (LaurentPolynomial R) B b

/-- The actual Laurent action on the original overlap ring. -/
def laurentMap : LaurentPolynomial R →+* R ⊗[k] B :=
  (comparison k R B).toRingHom.comp
    (algebraMap (LaurentPolynomial R) (LaurentPolynomial R ⊗[LaurentPolynomial k] B))

instance laurentAlgebra : Algebra (LaurentPolynomial R) (R ⊗[k] B) :=
  (laurentMap k R B).toAlgebra

def laurentComparison : LaurentPolynomial R ⊗[LaurentPolynomial k] B ≃ₐ[LaurentPolynomial R]
    R ⊗[k] B where
  __ := (comparison k R B).toRingEquiv
  commutes' _ := rfl

lemma laurentMap_C (r : R) : laurentMap k R B (C r) = r ⊗ₜ[k] (1 : B) := by
  change comparison k R B (algebraMap (LaurentPolynomial R)
    (LaurentPolynomial R ⊗[LaurentPolynomial k] B) (algebraMap R (LaurentPolynomial R) r)) = _
  rw [← IsScalarTower.algebraMap_apply R (LaurentPolynomial R)
    (LaurentPolynomial R ⊗[LaurentPolynomial k] B)]
  exact (comparison k R B).commutes r

instance coefficientTower : IsScalarTower R (LaurentPolynomial R) (R ⊗[k] B) :=
  IsScalarTower.of_algebraMap_eq' (by ext r; exact (laurentMap_C k R B r).symm)

/-- Every original Laurent monomial is preserved, not only the positive
polynomial coordinate. This is the reciprocal-chart normalization too. -/
lemma laurentMap_T (n : ℤ) : laurentMap k R B (T n) =
    (1 : R) ⊗ₜ[k] (algebraMap (LaurentPolynomial k) B (T n)) := by
  have h : algebraMap (LaurentPolynomial R)
      (LaurentPolynomial R ⊗[LaurentPolynomial k] B) (T n) =
      (1 : LaurentPolynomial R) ⊗ₜ[LaurentPolynomial k]
        (algebraMap (LaurentPolynomial k) B (T n)) := by
    have ht := TensorProduct.smul_tmul (R := LaurentPolynomial k) (T n : LaurentPolynomial k)
      (1 : LaurentPolynomial R) (1 : B)
    simpa only [Algebra.smul_def,AddMonoidAlgebra.algebraMap_def,T,
      AddMonoidAlgebra.mapRingHom_single,map_one,mul_one] using ht
  change comparison k R B (algebraMap (LaurentPolynomial R)
    (LaurentPolynomial R ⊗[LaurentPolynomial k] B) (T n)) = _
  rw [h,comparison_unit]
end RelativeOriginalLaurentAlgebra318
