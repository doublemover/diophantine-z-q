module
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Finite
public section
noncomputable section
namespace RelativeOriginalPolynomialAlgebra318
open Polynomial
open scoped TensorProduct
universe u
variable (k R B : Type u) [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra (Polynomial k) B]
  [IsScalarTower k (Polynomial k) B]
attribute [local instance] Polynomial.algebra

/-- The actual coefficient-base-changed original chart ring. -/
abbrev original := R ⊗[k] B
/-- The genuine polynomial-base-change presentation of that same chart. -/
abbrev presentation := Polynomial R ⊗[Polynomial k] B

/-- The actual polynomial pushout and its canonical tensor cancellation,
retaining both original coefficient and original chart maps. -/
def comparison : presentation k R B ≃ₐ[R] original k R B :=
  Algebra.IsPushout.cancelBaseChangeAlg k R (Polynomial k) (Polynomial R) B

lemma comparison_unit (b : B) : comparison k R B ((1 : Polynomial R) ⊗ₜ[Polynomial k] b) =
    (1 : R) ⊗ₜ[k] b :=
  Algebra.IsPushout.cancelBaseChangeAlg_tmul k R (Polynomial k) (Polynomial R) B b

/-- The polynomial action is the actual action induced by the canonical
pushout, not an arbitrary action assigned by finite generation. -/
def polynomialMap : Polynomial R →+* original k R B :=
  (comparison k R B).toRingHom.comp (algebraMap (Polynomial R) (presentation k R B))

instance polynomialAlgebra : Algebra (Polynomial R) (original k R B) :=
  (polynomialMap k R B).toAlgebra

/-- The same canonical ring comparison is linear for the displayed
original polynomial action. -/
def polynomialComparison : presentation k R B ≃ₐ[Polynomial R] original k R B where
  __ := (comparison k R B).toRingEquiv
  commutes' _ := rfl

lemma polynomialMap_C (r : R) : polynomialMap k R B (Polynomial.C r) = r ⊗ₜ[k] (1 : B) := by
  change comparison k R B (algebraMap (Polynomial R) (presentation k R B) (algebraMap R (Polynomial R) r)) = _
  rw [← IsScalarTower.algebraMap_apply R (Polynomial R) (presentation k R B)]
  exact (comparison k R B).commutes r

/-- The polynomial coefficient action is the SAME original R action on
R tensor B, not merely an isomorphic action. -/
instance coefficientTower : IsScalarTower R (Polynomial R) (original k R B) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (polynomialMap_C k R B r).symm)

/-- The original polynomial coordinate remains the original chart
coordinate after coefficient base change. -/
lemma polynomialMap_X : polynomialMap k R B Polynomial.X =
    (1 : R) ⊗ₜ[k] (algebraMap (Polynomial k) B Polynomial.X) := by
  have h : algebraMap (Polynomial R) (presentation k R B) Polynomial.X =
      (1 : Polynomial R) ⊗ₜ[Polynomial k] (algebraMap (Polynomial k) B Polynomial.X) := by
    have ht := TensorProduct.smul_tmul (Polynomial.X : Polynomial k)
      (1 : Polynomial R) (1 : B)
    simpa only [Algebra.smul_def,Polynomial.algebraMap_def,Polynomial.map_X,mul_one] using ht
  change comparison k R B (algebraMap (Polynomial R) (presentation k R B) Polynomial.X) = _
  rw [h,comparison_unit]

/-- Finite original chart algebras remain finite over the ACTUAL new
polynomial base, for arbitrary coefficient rings, including nonreduced ones. -/
instance finite [Module.Finite (Polynomial k) B] :
    Module.Finite (Polynomial R) (original k R B) := by
  letI : Module.Finite (Polynomial R) (presentation k R B) := inferInstance
  exact Module.Finite.of_surjective (polynomialComparison k R B).toLinearMap
    (polynomialComparison k R B).surjective
end RelativeOriginalPolynomialAlgebra318
