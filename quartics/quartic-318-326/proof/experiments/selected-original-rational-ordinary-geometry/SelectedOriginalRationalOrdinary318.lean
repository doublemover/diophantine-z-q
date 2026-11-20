module
public import SelectedRationalGenericFromComplex318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
open Polynomial
open scoped nonZeroDivisors
open SelectedRationalGenericFromComplex318

namespace SelectedOriginalRationalOrdinary318

@[expose] def denominator : ℚ[X] := X * (X - C 1728)
abbrev Base := Localization.Away denominator

@[expose] def jCoord : Base := algebraMap ℚ[X] Base X

private theorem nonzero_support : Submonoid.powers denominator ≤ nonZeroDivisors ℚ[X] := by
  intro f hf
  obtain ⟨r,rfl⟩ := hf
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  exact pow_ne_zero r (mul_ne_zero Polynomial.X_ne_zero
    (by simpa using Polynomial.X_sub_C_ne_zero (1728 : ℚ)))

/-- The actual ordinary rational base is the principal open of
the original chart j, with no extra j-denominator for 6N. -/
@[expose] def ratscalar : Algebra Base QJ :=
  IsLocalization.localizationAlgebraOfSubmonoidLe Base QJ
    (Submonoid.powers denominator) (nonZeroDivisors ℚ[X]) (by exact nonzero_support)

theorem rattower :
    letI : Algebra Base QJ := ratscalar
    IsScalarTower ℚ[X] Base QJ :=
  IsLocalization.localization_isScalarTower_of_submonoid_le Base QJ
    (Submonoid.powers denominator) (nonZeroDivisors ℚ[X]) nonzero_support

theorem ratFraction :
    letI : Algebra Base QJ := ratscalar
    IsFractionRing Base QJ := by
  letI : Algebra Base QJ := ratscalar
  letI : IsScalarTower ℚ[X] Base QJ := rattower
  exact IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers denominator)
    Base QJ nonzero_support

@[expose] def originalPolynomial : ℤ[X] →+* ℚ[X] :=
  Polynomial.mapRingHom (Int.castRingHom ℚ)

@[expose] def scalarPolynomial : ℤ[X] →+* Base :=
  (algebraMap ℚ[X] Base).comp originalPolynomial

private theorem scalarUnit (N : ℕ) [NeZero N] :
    IsUnit (scalarPolynomial (OpenJModel318.denominator N)) := by
  have he : originalPolynomial (OpenJModel318.denominator N) =
      (6 * (N : ℚ[X])) * denominator := by
    simp [originalPolynomial,OpenJModel318.denominator,denominator,mul_assoc]
  have h6 : IsUnit (6 : ℚ[X]) := by
    simpa only [map_ofNat] using
      ((isUnit_iff_ne_zero.mpr (by norm_num : (6 : ℚ) ≠ 0)).map (C : ℚ →+* ℚ[X]))
  have hN : IsUnit (N : ℚ[X]) := by
    have hn : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    simpa only [map_natCast] using ((isUnit_iff_ne_zero.mpr hn).map (C : ℚ →+* ℚ[X]))
  change IsUnit (algebraMap ℚ[X] Base (originalPolynomial (OpenJModel318.denominator N)))
  rw [he,map_mul]
  exact ((h6.mul hN).map (algebraMap ℚ[X] Base)).mul
    (IsLocalization.Away.algebraMap_isUnit (S := Base) denominator)

/-- Scalar change of the original coefficient ring, before passing
to the whole generic field or forming an ordinary root algebra. -/
@[expose] def toRational (N : ℕ) [NeZero N] : OpenJModel318.Base N →+* Base :=
  IsLocalization.Away.lift (OpenJModel318.denominator N) (by exact scalarUnit N)

theorem toRational_j (N : ℕ) [NeZero N] :
    toRational N (OpenJModel318.jCoord N) = jCoord := by
  rw [OpenJModel318.jCoord,toRational,IsLocalization.Away.lift_eq]
  simp [scalarPolynomial,originalPolynomial,jCoord]

/-- Both routes agree on the ENTIRE localized original base,
for the same literal j, so its actual monic polynomial has
the same coefficients in Q(J) by either route. -/
theorem generic_factor (N : ℕ) [NeZero N] :
    letI : Algebra Base QJ := ratscalar
    (algebraMap Base QJ).comp (toRational N) = rationalGenericMap N := by
  letI : Algebra Base QJ := ratscalar
  letI : IsScalarTower ℚ[X] Base QJ := rattower
  apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · change algebraMap Base QJ (toRational N (OpenJModel318.jCoord N)) =
      rationalGenericMap N (OpenJModel318.jCoord N)
    rw [toRational_j,jCoord,← IsScalarTower.algebraMap_apply,RatFunc.algebraMap_X,rationalGenericMap_j]

end SelectedOriginalRationalOrdinary318

#print axioms SelectedOriginalRationalOrdinary318.ratFraction
#print axioms SelectedOriginalRationalOrdinary318.generic_factor
