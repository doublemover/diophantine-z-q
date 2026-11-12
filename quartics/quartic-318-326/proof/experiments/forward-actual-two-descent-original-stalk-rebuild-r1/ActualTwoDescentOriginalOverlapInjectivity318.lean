module
public import ActualTwoDescentOriginalOverlapEquivalence318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapInjectivity318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentInfinityNativeDomain318 ActualTwoDescentOriginalPuncturedCharts318
open ActualTwoDescentOriginalOverlapQuotientMaps318 ActualTwoDescentOriginalOverlapLocalizationMaps318
open ActualTwoDescentOriginalOverlapEquivalence318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_affine_open_injective (n : K) : Function.Injective (affineOpenMap n) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (actual_affine_y_nonzero n))
lemma actual_infinity_open_injective (n : K) : Function.Injective (infinityOpenMap n) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (actual_chart_v_nonzero n))

/-- Injectivity of reciprocal-coordinate substitution is now proved
from the literal overlap equivalence and the native denominator maps. -/
lemma actual_affine_to_infinity_injective (n : K) : Function.Injective (affineToInfinity n) := by
  intro x y h
  apply actual_affine_open_injective n
  apply (originalOverlapEquiv n).injective
  change affineOverlapMap n (affineOpenMap n x)=affineOverlapMap n (affineOpenMap n y)
  simpa only [actual_affine_overlap_base] using h

lemma actual_infinity_to_affine_injective (n : K) : Function.Injective (infinityToAffine n) := by
  intro x y h
  apply actual_infinity_open_injective n
  apply (originalOverlapEquiv n).symm.injective
  change infinityOverlapMap n (infinityOpenMap n x)=infinityOverlapMap n (infinityOpenMap n y)
  simpa only [actual_infinity_overlap_base] using h
end ActualTwoDescentOriginalOverlapInjectivity318
