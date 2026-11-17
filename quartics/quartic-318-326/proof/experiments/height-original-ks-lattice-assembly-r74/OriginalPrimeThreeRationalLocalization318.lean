module
public import OriginalPrimeThreeLocalOrderQuotient318
public import OriginalIntegerFractionField318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace OriginalPrimeThreeRationalLocalization318
open OriginalPrimeThreeLocalOrderQuotient318
abbrev twist := OriginalPrimeThreeActualQuotient318.twist
abbrev RationalOrder := ContactKummerOrder318.SourceOrder twist
attribute [local instance] OriginalIntegerFractionField318.rationalOrderAlgebra
abbrev integerDenominators : Submonoid Order :=
  Algebra.algebraMapSubmonoid Order (nonZeroDivisors ℤ)

/-- The existing rational-order localization in polynomial coefficients
inverts precisely nonzero integers, not the polynomial parameter. -/
theorem integer_denominators :
    Algebra.algebraMapSubmonoid Order IntegerPolynomialLocalization318.denominators =
      integerDenominators := by
  ext z
  constructor
  · rintro ⟨p, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, IsScalarTower.algebraMap_apply ℤ (Polynomial ℤ) Order n⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨algebraMap ℤ (Polynomial ℤ) n, ⟨n, hn, rfl⟩,
      (IsScalarTower.algebraMap_apply ℤ (Polynomial ℤ) Order n).symm⟩

instance rational_order_localization : IsLocalization integerDenominators RationalOrder := by
  rw [← integer_denominators]
  exact OriginalIntegerFractionField318.rational_order_localization twist

theorem denominators_le : denominators ≤ integerDenominators := by
  rintro x ⟨s, hs, rfl⟩
  exact ⟨s, PrimeThreeCoefficientLocalization318.primeIdeal.primeCompl_le_nonZeroDivisors hs, rfl⟩

/-- The native lift of the exact original-order rational inclusion. -/
@[expose] def rationalAlgebra : Algebra LocalOrder RationalOrder :=
  IsLocalization.localizationAlgebraOfSubmonoidLe LocalOrder RationalOrder
    denominators integerDenominators denominators_le
attribute [local instance] rationalAlgebra

instance rational_tower : IsScalarTower Order LocalOrder RationalOrder :=
  IsLocalization.localization_isScalarTower_of_submonoid_le LocalOrder RationalOrder
    denominators integerDenominators denominators_le

abbrev rationalDenominators : Submonoid LocalOrder :=
  integerDenominators.map (algebraMap Order LocalOrder)
abbrev pivot : LocalOrder := algebraMap Order LocalOrder (3 : Order)

private theorem integer_coeff (n : ℤ) :
    algebraMap Order LocalOrder (algebraMap ℤ Order n) = algebraMap ℤ LocalOrder n :=
  (IsScalarTower.algebraMap_apply ℤ Order LocalOrder n).symm

theorem pivot_powers_le : Submonoid.powers pivot ≤ rationalDenominators := by
  rintro x ⟨n, rfl⟩
  refine ⟨algebraMap ℤ Order ((3 : ℤ) ^ n), ?_, ?_⟩
  · exact ⟨(3 : ℤ) ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero n (by norm_num)), rfl⟩
  · simp only [map_pow, map_ofNat, pivot]

/-- Every remaining coefficient denominator divides a power of three in
this exact local order, since its prime-to-three factor is already a unit. -/
theorem rational_denominator_dvd_pivot (x : LocalOrder) (hx : x ∈ rationalDenominators) :
    ∃ y ∈ Submonoid.powers pivot, x ∣ y := by
  obtain ⟨a, ⟨d, hd, rfl⟩, rfl⟩ := hx
  obtain ⟨n, s, hds, hs⟩ := PrimeThreeCoefficientLocalization318.denominator_factor d
    (mem_nonZeroDivisors_iff_ne_zero.mp hd)
  have hu : IsUnit (algebraMap ℤ LocalOrder s) := by
    rw [← integer_coeff]
    exact IsLocalization.map_units LocalOrder
      ⟨algebraMap ℤ Order s, ⟨s, hs, rfl⟩⟩
  obtain ⟨u, hu⟩ := hu
  refine ⟨pivot ^ n, ⟨n, rfl⟩, ⟨↑u⁻¹, ?_⟩⟩
  rw [hds]
  simp only [map_mul, map_pow, map_ofNat, integer_coeff, ← hu]
  simp [pivot, mul_assoc]

/-- Inverting three in the actual Z_(3) coefficient order gives the WHOLE
original rational four-root order, with the original embedding retained. -/
theorem actual_rational_away : IsLocalization.Away pivot RationalOrder := by
  letI : IsLocalization rationalDenominators RationalOrder :=
    IsLocalization.isLocalization_of_submonoid_le (S := LocalOrder) (T := RationalOrder)
      denominators integerDenominators denominators_le
  exact (IsLocalization.iff_of_le_of_exists_dvd
    (M := Submonoid.powers pivot) (S := RationalOrder) rationalDenominators
    pivot_powers_le rational_denominator_dvd_pivot).mpr inferInstance

end OriginalPrimeThreeRationalLocalization318
