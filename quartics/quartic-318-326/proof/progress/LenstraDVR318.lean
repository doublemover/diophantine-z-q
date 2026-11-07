module
public import LenstraDifferent318
public section
noncomputable section
namespace LenstraDVR318
open Module Algebra IsDiscreteValuationRing Submodule.IsPrincipal

variable (A K B L:Type*) [CommRing A] [IsDomain A] [Field K]
    [CommRing B] [IsDomain B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [Algebra A B] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [CharZero K] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [IsTorsionFree A B] [IsFractionRing B L] [IsDiscreteValuationRing B]

/-- The actual DVR exponent of the actual different is strictly less than
the value of n times a nonzero base nonunit. -/
theorem different_value_lt (x:A) (hx:x≠0) (hunit:¬IsUnit x) :
    addVal B (generator (differentIdeal A B)) <
      addVal B (Module.finrank K L:B) + addVal B (algebraMap A B x) := by
  have h := LenstraDifferent318.different_not_le_degree_mul A K B L x hx hunit
  let b:B := (Module.finrank K L:B)*algebraMap A B x
  have h':¬ idealOrderIsoENat B (differentIdeal A B) ≤
      idealOrderIsoENat B (Ideal.span {b}) := by
    simpa only [OrderIso.le_iff_le] using h
  change ¬ addVal B (generator (Ideal.span {b})) ≤
    addVal B (generator (differentIdeal A B)) at h'
  have hg:addVal B (generator (Ideal.span {b}))=addVal B b :=
    (addVal_eq_iff_associated _ _).mpr (associated_generator_span_self b)
  rw [hg] at h'
  simpa only [b,addVal_mul] using lt_of_not_ge h'

end LenstraDVR318
