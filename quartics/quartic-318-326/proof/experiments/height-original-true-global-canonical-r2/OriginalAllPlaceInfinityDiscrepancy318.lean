module
public import OriginalInfinityGlobalSections318
public import OriginalInfinityRatioClosedBase318
public import OriginalWholeIntrinsicSections318
public section
noncomputable section
namespace OriginalAllPlaceInfinityDiscrepancy318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c t w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "q" => OriginalInfinityRatioParameters318.common V D.coefficients a
local notation "r" => OriginalInfinityRatioParameters318.ratios V D.coefficients a

/-- At each original arithmetic place, the SAME global intrinsic sections
have produced integral ratio-order extensions on the SPECIFIED pivot open.
This is not a claim that the pivot open contains every bad-prime center. -/
theorem original_global_extensions :
    (OriginalInfinityGlobalSections318.genericImage V D.coefficients a
      (OriginalWholeIntrinsicSections318.global0 c t w D)=
      FourRootRatioPuncturedSections318.ratioExtension q r
        (OriginalInfinityRatioSections318.section0 V D.coefficients a)) ∧
    (OriginalInfinityGlobalSections318.genericImage V D.coefficients a
      (OriginalWholeIntrinsicSections318.global1 c t w D)=
      FourRootRatioPuncturedSections318.ratioExtension q r
        (OriginalInfinityRatioSections318.section1 V D.coefficients a)) :=
  ⟨OriginalInfinityGlobalSections318.global0_image V D.coefficients a,
    OriginalInfinityGlobalSections318.global1_image V D.coefficients a⟩

/-- The precise closed-infinity coverage condition is kept as such.
No nonunit pivot is silently inverted at an original arithmetic center. -/
@[expose] def infinityBase (h0 : IsUnit (D.coefficients 0)) :
    OriginalInfinityRatioParameters318.Base V D.coefficients a →+* V :=
  OriginalInfinityRatioClosedBase318.atInfinity V D.coefficients a h0
end OriginalAllPlaceInfinityDiscrepancy318
