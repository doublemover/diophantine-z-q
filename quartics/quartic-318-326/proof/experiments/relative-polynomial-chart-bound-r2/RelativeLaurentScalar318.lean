module
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Span.Defs
public section
noncomputable section
namespace RelativeLaurentScalar318
open LaurentPolynomial
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]

/-- The coefficient action is the actual restriction along Laurent C,
not a structure transported through a chosen free presentation. -/
@[expose] def coefficientModule : Module R M := Module.compHom M (C : R →+* LaurentPolynomial R)
local instance : Module R M := coefficientModule R M

lemma constant_smul (a : R) (x : M) : (C a : LaurentPolynomial R) • x = a • x := rfl

lemma shift_add (a b : ℤ) (x : M) :
    (T a : LaurentPolynomial R) • ((T b : LaurentPolynomial R) • x) =
      (T (a+b) : LaurentPolynomial R) • x := by
  rw [smul_smul,← T_add]

lemma shift_constant (a b : ℤ) (c : R) (x : M) :
    (T a : LaurentPolynomial R) • ((C c * T b : LaurentPolynomial R) • x) =
      c • ((T (a+b) : LaurentPolynomial R) • x) := by
  rw [← constant_smul R M,smul_smul,smul_smul]
  congr 1
  rw [← mul_assoc,mul_comm (T a) (C c),mul_assoc,← T_add]

/-- Actual Laurent monomial multiplication as a coefficient-linear map. -/
def shift (a : ℤ) : M →ₗ[R] M where
  toFun x := (T a : LaurentPolynomial R) • x
  map_add' := smul_add _
  map_smul' c x := by
    change (T a : LaurentPolynomial R) • ((C c : LaurentPolynomial R) • x) =
      (C c : LaurentPolynomial R) • ((T a : LaurentPolynomial R) • x)
    exact smul_comm _ _ _
end RelativeLaurentScalar318
