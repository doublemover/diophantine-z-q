module
public import IntegerPolynomialLocalization318
public import FractionFieldLocalizationDescent318
public import Mathlib.FieldTheory.RatFunc.Basic
public section
noncomputable section
namespace IntegerPolynomialFractionField318
open Polynomial
attribute [local instance] OriginalIntegerAffineModel318.rationalPolynomialAlgebra

/-- The parameter-preserving inclusion into Q(T), through Q[T]. -/
@[expose] def fieldAlgebra : Algebra ℤ[X] (RatFunc ℚ) :=
  ((algebraMap ℚ[X] (RatFunc ℚ)).comp (algebraMap ℤ[X] ℚ[X])).toAlgebra
attribute [local instance] fieldAlgebra

theorem scalar_tower : IsScalarTower ℤ[X] ℚ[X] (RatFunc ℚ) := by
  infer_instance

theorem polynomial_injective : Function.Injective (algebraMap ℤ[X] ℚ[X]) := by
  intro p q h
  apply Polynomial.ext
  intro n
  have hn := congrArg (fun f : ℚ[X] => f.coeff n) h
  change (p.map (Int.castRingHom ℚ)).coeff n = (q.map (Int.castRingHom ℚ)).coeff n at hn
  simp only [Polynomial.coeff_map] at hn
  exact Int.cast_injective hn

/-- Q(T) is the actual fraction field of Z[T], not just of Q[T]. -/
theorem actual_fractionField : IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI : SMul ℤ[X] (RatFunc ℚ) := fieldAlgebra.toSMul
  letI : IsScalarTower ℤ[X] ℚ[X] (RatFunc ℚ) :=
    IsScalarTower.of_algebraMap_eq' (R := ℤ[X]) (S := ℚ[X]) (A := RatFunc ℚ) rfl
  letI : FaithfulSMul ℤ[X] (RatFunc ℚ) :=
    (faithfulSMul_iff_algebraMap_injective ℤ[X] (RatFunc ℚ)).mpr
      ((IsFractionRing.injective ℚ[X] (RatFunc ℚ)).comp polynomial_injective)
  letI : IsLocalization IntegerPolynomialLocalization318.denominators ℚ[X] :=
    IntegerPolynomialLocalization318.rational_polynomial_localization
  exact FractionFieldLocalizationDescent318.of_localization (S := ℚ[X])
    IntegerPolynomialLocalization318.denominators
end IntegerPolynomialFractionField318
