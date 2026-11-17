module
public import OriginalIntegerReciprocalNormalization318
public import FractionFieldLocalizationDescent318
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace OriginalIntegerReciprocalFractionField318
open Polynomial
attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.laurentAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev L := OriginalIntegerFiniteClosure318.L c
abbrev Overlap := OriginalIntegerNormalizedOverlap318.Overlap c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- The common normalized overlap retains the actual original function
field, derived by localization of the finite normalization chart. -/
theorem overlap_fractionField : IsFractionRing (Overlap c) (L c) := by
  letI := OriginalIntegerNormalizedOverlap318.overlapAlgebra c
  letI : IsScalarTower (OriginalIntegerFiniteClosure318.Closure c) (Overlap c) (L c) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI := OriginalIntegerNormalizedOverlap318.overlap_localization c
  letI := OriginalIntegerFiniteClosure318.closure_fractionField c
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (algebraMap ℤ[X] (OriginalIntegerFiniteClosure318.Closure c) X))
    (Overlap c) (L c)

attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalLaurentAlgebra
abbrev ReciprocalClosure := OriginalIntegerReciprocalNormalization318.Closure c

/-- Descend the common overlap fraction-field theorem through the actual
reciprocal localization. No field identification is added as a premise. -/
theorem reciprocal_fractionField : IsFractionRing (ReciprocalClosure c) (L c) := by
  letI := OriginalIntegerReciprocalNormalization318.overlapAlgebra c
  letI : IsScalarTower (ReciprocalClosure c) (Overlap c) (L c) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI := OriginalIntegerReciprocalNormalization318.overlap_localization c
  letI := overlap_fractionField c
  exact FractionFieldLocalizationDescent318.of_localization (S := Overlap c)
    (Submonoid.powers (algebraMap ℤ[X] (ReciprocalClosure c) X))

/-- Integrally closedness is a genuine consequence of being an integral
closure inside a field, via native transitivity. It is NOT regularity. -/
theorem reciprocal_normal : IsIntegrallyClosed (ReciprocalClosure c) :=
  IsIntegrallyClosed.of_isIntegrallyClosedIn (ReciprocalClosure c) (L c)

theorem overlap_normal : IsIntegrallyClosed (Overlap c) :=
  IsIntegrallyClosed.of_isIntegrallyClosedIn (Overlap c) (L c)

end OriginalIntegerReciprocalFractionField318
