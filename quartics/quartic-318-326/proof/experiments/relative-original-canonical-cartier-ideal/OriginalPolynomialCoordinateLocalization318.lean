module
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace OriginalPolynomialCoordinateLocalization318
open TensorProduct LaurentPolynomial
open scoped TensorProduct
universe u v w
variable (R : Type u) [CommRing R]
  (f : Polynomial R →+* LaurentPolynomial R)
local instance : Algebra (Polynomial R) (LaurentPolynomial R) := f.toAlgebra
variable (N : Type v) [AddCommGroup N] [Module (Polynomial R) N]
  (M : Type w) [AddCommGroup M] [Module (LaurentPolynomial R) M]
  (e : LaurentPolynomial R ⊗[Polynomial R] N ≃ₗ[LaurentPolynomial R] M)
  {r : ℕ} (out : N →ₗ[Polynomial R] Fin r → Polynomial R)

/-- Localize the specified ORIGINAL polynomial coordinate map using
the specified genuine section-localization isomorphism. -/
@[expose] def map : M →ₗ[LaurentPolynomial R] Fin r → LaurentPolynomial R :=
  (TensorProduct.piScalarRight (Polynomial R) (LaurentPolynomial R) (LaurentPolynomial R) (Fin r)).toLinearMap.comp
    ((out.baseChange (LaurentPolynomial R)).comp e.symm.toLinearMap)

lemma unit (x : N) : map R f N M e out (e ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x)) =
    fun i => f (out x i) := by
  change TensorProduct.piScalarRight (Polynomial R) (LaurentPolynomial R) (LaurentPolynomial R) (Fin r)
    ((out.baseChange (LaurentPolynomial R)) (e.symm (e ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x)))) = _
  rw [LinearEquiv.symm_apply_apply,LinearMap.baseChange_tmul,
    TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul]
  funext i
  change f (out x i) * 1 = f (out x i)
  exact mul_one _
end OriginalPolynomialCoordinateLocalization318
