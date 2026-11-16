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

/-- The coefficientwise rational polynomial algebra is the actual integer
coefficient localization, with the named coefficient algebra fixed. -/
theorem rational_polynomial_localization : IsLocalization denominators ℚ[X] := by
  rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ) ℚ,
    Algebra.IsPushout.comm]
  infer_instance

end IntegerPolynomialLocalization318
