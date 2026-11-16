module
public import OriginalIntegerAffineModel318
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.PolynomialAlgebra
public section
noncomputable section
namespace IntegerPolynomialLocalization318
open Polynomial
attribute [local instance] OriginalIntegerAffineModel318.rationalPolynomialAlgebra

/-- Only nonzero integer constants are inverted. The variable is not inverted. -/
abbrev denominators : Submonoid ℤ[X] :=
  Algebra.algebraMapSubmonoid ℤ[X] (nonZeroDivisors ℤ)

/-- The named coefficient map is exactly the native polynomial algebra.
The equality is explicit because typeclass matching does not unfold the
named semireducible algebra while searching for the polynomial pushout. -/
theorem rationalPolynomialAlgebra_eq_native :
    OriginalIntegerAffineModel318.rationalPolynomialAlgebra = Polynomial.algebra ℤ ℚ :=
  algebra_ext _ _ (fun _ => rfl)

/-- The coefficientwise rational polynomial algebra is the actual integer
coefficient localization, with the named coefficient algebra fixed. -/
theorem rational_polynomial_localization : IsLocalization denominators ℚ[X] := by
  letI : Algebra ℤ[X] ℚ[X] := Polynomial.algebra ℤ ℚ
  have h : IsLocalization denominators ℚ[X] := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ) ℚ,
      Algebra.IsPushout.comm]
    infer_instance
  simpa only [rationalPolynomialAlgebra_eq_native] using h

end IntegerPolynomialLocalization318
