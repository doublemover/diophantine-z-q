module
public import OriginalPrimeThreeActualQuotient318
public import PrimeThreeCoefficientLocalization318
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.LocalProperties.Reduced
public section
noncomputable section
namespace OriginalPrimeThreeLocalOrderQuotient318

abbrev Order := OriginalPrimeThreeActualQuotient318.Order
/-- Only integer coefficients prime to three are inverted. No parameter,
branch root, or function vanishing at a prospective point is inverted. -/
abbrev denominators : Submonoid Order := Algebra.algebraMapSubmonoid Order
  PrimeThreeCoefficientLocalization318.primeIdeal.primeCompl
abbrev LocalOrder := Localization denominators
abbrev divisor : Ideal Order := Ideal.span {(3 : Order)}

/-- This is the literal local coefficient order's divisor ideal. -/
theorem divisor_map : divisor.map (algebraMap Order LocalOrder) =
    Ideal.span {(3 : LocalOrder)} := by
  simp only [divisor, Ideal.map_span, Set.image_singleton, map_ofNat]

/-- Quotient then localization and localization then quotient agree on
this exact denominator set, using the native quotient algebra action. -/
theorem quotient_localization :
    IsLocalization (Algebra.algebraMapSubmonoid (Order ⧸ divisor) denominators)
      (LocalOrder ⧸ divisor.map (algebraMap Order LocalOrder)) := inferInstance

/-- Actual reducedness of the coefficient-localized original order mod 3.
This is not a conclusion about the normalization or a closed-point local ring. -/
theorem actual_local_quotient_reduced :
    IsReduced (LocalOrder ⧸ Ideal.span {(3 : LocalOrder)}) := by
  rw [← divisor_map]
  letI : IsReduced (Order ⧸ divisor) :=
    OriginalPrimeThreeActualQuotient318.actual_quotient_reduced
  letI := quotient_localization
  exact isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid (Order ⧸ divisor) denominators)
    (LocalOrder ⧸ divisor.map (algebraMap Order LocalOrder)) inferInstance

end OriginalPrimeThreeLocalOrderQuotient318
