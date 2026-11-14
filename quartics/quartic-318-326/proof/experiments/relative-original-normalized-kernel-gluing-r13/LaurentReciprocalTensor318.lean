module
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace LaurentReciprocalTensor318
open LaurentPolynomial
open scoped TensorProduct
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra (Polynomial R) B]

@[expose] def reciprocalAlgebra : Algebra (Polynomial R) (LaurentPolynomial R) :=
  ((LaurentPolynomial.invert (R := R)).toRingHom.comp Polynomial.toLaurent).toAlgebra

@[expose] def reciprocal : Type u :=
  letI := reciprocalAlgebra R
  LaurentPolynomial R ⊗[Polynomial R] B
instance : CommRing (reciprocal R B) := by
  delta reciprocal
  infer_instance

instance : Algebra (LaurentPolynomial R) (reciprocal R B) := by
  delta reciprocal
  infer_instance
instance : Algebra R (reciprocal R B) :=
  ((algebraMap (LaurentPolynomial R) (reciprocal R B)).comp LaurentPolynomial.C).toAlgebra

/-- The two Laurent factors carry DIFFERENT polynomial actions. The
coordinate inversion explicitly intertwines them; they are not identified. -/
@[expose] def factor : @AlgEquiv (Polynomial R) (LaurentPolynomial R) (LaurentPolynomial R)
    _ _ _ (LaurentPolynomial.algebraPolynomial R) (reciprocalAlgebra R) where
  __ := (LaurentPolynomial.invert (R := R)).toRingEquiv
  commutes' _ := rfl

@[expose] def equivalence : (LaurentPolynomial R ⊗[Polynomial R] B) ≃+* reciprocal R B :=
  (Algebra.TensorProduct.congr (factor R) (AlgEquiv.refl : B ≃ₐ[Polynomial R] B)).toRingEquiv

lemma tmul (l : LaurentPolynomial R) (b : B) :
    equivalence R B (l ⊗ₜ[Polynomial R] b) =
      letI := reciprocalAlgebra R
      (LaurentPolynomial.invert l) ⊗ₜ[Polynomial R] b := by
  rfl

lemma right (b : B) :
    equivalence R B ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] b) =
      letI := reciprocalAlgebra R
      (1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] b := by
  rw [tmul,map_one]

lemma symm_tmul (l : LaurentPolynomial R) (b : B) :
    (equivalence R B).symm (letI := reciprocalAlgebra R; l ⊗ₜ[Polynomial R] b) =
      (LaurentPolynomial.invert l) ⊗ₜ[Polynomial R] b := by
  apply (equivalence R B).injective
  rw [RingEquiv.apply_symm_apply,tmul,LaurentPolynomial.involutive_invert]

lemma scalar (l : LaurentPolynomial R) (z : LaurentPolynomial R ⊗[Polynomial R] B) :
    equivalence R B (l • z) = LaurentPolynomial.invert l • equivalence R B z := by
  change equivalence R B ((l ⊗ₜ[Polynomial R] (1 : B)) * z) =
    algebraMap (LaurentPolynomial R) (reciprocal R B) (LaurentPolynomial.invert l) * equivalence R B z
  rw [map_mul,tmul]
  rfl
end LaurentReciprocalTensor318
