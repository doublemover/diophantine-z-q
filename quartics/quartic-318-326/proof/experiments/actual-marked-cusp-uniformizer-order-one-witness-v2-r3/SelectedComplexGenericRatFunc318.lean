module
public import SelectedComplexOrdinaryOneField318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.FieldTheory.RatFunc.Basic
public section
noncomputable section
open Polynomial
open scoped nonZeroDivisors
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318

namespace SelectedComplexGenericRatFunc318

theorem inversion_support :
    Submonoid.powers denominator ≤ nonZeroDivisors ℂ[X] := by
  intro f hf
  obtain ⟨r,rfl⟩ := hf
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  exact pow_ne_zero r (mul_ne_zero Polynomial.X_ne_zero
    (by
      rw [←(Polynomial.C_ofNat (R := ℂ) 1728)]
      exact Polynomial.X_sub_C_ne_zero (1728 : ℂ)))

/-- Rational-function algebra via the very same polynomial localization,
without a different abstract copy of the projective base coordinate. -/
@[expose] def ratscalar : Algebra Base (RatFunc ℂ) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe Base (RatFunc ℂ)
    (Submonoid.powers denominator) (nonZeroDivisors ℂ[X]) inversion_support

theorem rattower :
    letI : Algebra Base (RatFunc ℂ) := ratscalar
    IsScalarTower ℂ[X] Base (RatFunc ℂ) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le Base (RatFunc ℂ)
    (Submonoid.powers denominator) (nonZeroDivisors ℂ[X]) inversion_support

/-- The generic coefficient field used in the whole root algebra is
literally the usual ℂ(J), with the original J unchanged. -/
@[expose] def ratEquiv :
    letI : Algebra Base (RatFunc ℂ) := ratscalar
    Generic ≃ₐ[Base] RatFunc ℂ := by
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  letI : IsScalarTower ℂ[X] Base (RatFunc ℂ) := rattower
  letI : IsFractionRing Base (RatFunc ℂ) :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers denominator)
      Base (RatFunc ℂ) inversion_support
  exact FractionRing.algEquiv Base (RatFunc ℂ)

theorem ratEquiv_literal_j :
    letI : Algebra Base (RatFunc ℂ) := ratscalar
    ratEquiv (algebraMap Base Generic jCoord) =
      algebraMap ℂ[X] (RatFunc ℂ) (X : ℂ[X]) := by
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  letI : IsScalarTower ℂ[X] Base (RatFunc ℂ) := rattower
  rw [AlgEquiv.commutes,jCoord,← IsScalarTower.algebraMap_apply]

end SelectedComplexGenericRatFunc318

#print axioms SelectedComplexGenericRatFunc318.ratEquiv_literal_j
