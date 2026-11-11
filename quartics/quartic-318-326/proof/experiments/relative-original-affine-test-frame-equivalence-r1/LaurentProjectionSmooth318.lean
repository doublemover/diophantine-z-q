module
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace LaurentProjectionSmooth318
open AlgebraicGeometry CategoryTheory
universe u
variable (B : Type u) [CommRing B]

/-- The LITERAL Laurent algebra is smooth over its coefficient ring:
it is the actual one-variable polynomial algebra localized at X. -/
theorem algebra_smooth : Algebra.Smooth B (LaurentPolynomial B) := by
  letI : Algebra.Smooth B (Polynomial B) := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Smooth (Polynomial B) (LaurentPolynomial B) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial B)
  letI : IsScalarTower B (Polynomial B) (LaurentPolynomial B) :=
    IsScalarTower.of_algebraMap_eq (fun b => by
      change LaurentPolynomial.C b=Polynomial.toLaurent (Polynomial.C b)
      exact (Polynomial.toLaurent_C b).symm)
  exact Algebra.Smooth.comp B (Polynomial B) (LaurentPolynomial B)

/-- Actual Spec coefficient projection; no replacement affine map or
abstract smoothness assumption is supplied by a caller. -/
theorem smooth : Smooth (Spec.map
    (CommRingCat.ofHom (algebraMap B (LaurentPolynomial B)))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr (algebra_smooth B)
end LaurentProjectionSmooth318
