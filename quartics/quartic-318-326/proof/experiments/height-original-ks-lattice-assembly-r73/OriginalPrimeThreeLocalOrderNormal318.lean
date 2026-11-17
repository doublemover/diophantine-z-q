module
public import OriginalPrimeThreeRationalLocalization318
public import ReducedDivisorNormality318
public import SourceGlobalAffine318
public section
noncomputable section
namespace OriginalPrimeThreeLocalOrderNormal318
open OriginalPrimeThreeLocalOrderQuotient318 OriginalPrimeThreeRationalLocalization318
abbrev L := OriginalIntegerFractionField318.L twist
local instance sourceField : Field L :=
  (KummerTensorField318.source_raw_field twist).toField
local instance orderDomain : IsDomain Order :=
  OriginalIntegerAffineModel318.order_domain twist
local instance rationalDomain : IsDomain RationalOrder :=
  ContactKummerOrder318.source_domain twist
attribute [local instance] OriginalIntegerFractionField318.rationalOrderAlgebra
attribute [local instance] OriginalIntegerFractionField318.rationalFieldAlgebra
attribute [local instance] OriginalIntegerFractionField318.integerFieldAlgebra
attribute [local instance] OriginalPrimeThreeRationalLocalization318.rationalAlgebra

/-- The local coefficient order enters the original field through the
canonical rational lift and the original rational four-root embedding. -/
@[expose] def fieldMap : LocalOrder →+* L :=
  (algebraMap RationalOrder L).comp (algebraMap LocalOrder RationalOrder)
@[expose] def fieldAlgebra : Algebra LocalOrder L := fieldMap.toAlgebra
attribute [local instance] fieldAlgebra

instance rational_field_tower : @IsScalarTower LocalOrder RationalOrder L
    (rationalAlgebra).toSMul
    (OriginalIntegerFractionField318.rationalFieldAlgebra twist).toSMul
    fieldAlgebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := LocalOrder) (S := RationalOrder) (A := L) rfl

instance original_field_tower : @IsScalarTower Order LocalOrder L
    (inferInstance : Algebra Order LocalOrder).toSMul fieldAlgebra.toSMul
    (OriginalIntegerFractionField318.integerFieldAlgebra twist).toSMul := by
  apply IsScalarTower.of_algebraMap_eq' (R := Order) (S := LocalOrder) (A := L)
  change algebraMap Order L =
    ((algebraMap RationalOrder L).comp (algebraMap LocalOrder RationalOrder)).comp
      (algebraMap Order LocalOrder)
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq Order LocalOrder RationalOrder]
  rfl

theorem denominators_nonzero : denominators ≤ nonZeroDivisors Order := by
  intro x hx
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hzero
  have hu := (IsLocalization.map_units RationalOrder ⟨x, denominators_le hx⟩).map
    (algebraMap RationalOrder L)
  exact hu.ne_zero (by simp only [hzero, map_zero])

instance localOrderDomain : IsDomain LocalOrder :=
  IsLocalization.isDomain_of_le_nonZeroDivisors LocalOrder denominators_nonzero

/-- Both fields of fractions are the specified original Kummer field. -/
theorem local_fractionField : IsFractionRing LocalOrder L := by
  letI := OriginalIntegerFractionField318.actual_fractionField twist
  exact IsFractionRing.isFractionRing_of_isLocalization denominators LocalOrder L
    denominators_nonzero

theorem pivot_nonzero : pivot ≠ 0 := by
  letI := actual_rational_away
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := RationalOrder) pivot).map
    (algebraMap RationalOrder L)
  intro hzero
  exact hu.ne_zero (by simp only [hzero, map_zero])

/-- The ACTUAL coefficient-localized untwisted order is normal. The proof
uses its actual reduced mod-three quotient and whole rational order, not
normality of a generic field or an unspecified localization. -/
theorem localOrder_normal : IsIntegrallyClosed LocalOrder := by
  letI : IsReduced (LocalOrder ⧸ Ideal.span {pivot}) := by
    simpa only [pivot, map_ofNat] using actual_local_quotient_reduced
  letI := actual_rational_away
  letI := local_fractionField
  letI : IsFractionRing RationalOrder L := SourceFractionField318.actual_fractionField twist
  letI : IsIntegrallyClosed RationalOrder := SourceGlobalAffine318.source_integrallyClosed twist
  exact ReducedDivisorNormality318.normal_of_away (L := L) pivot pivot_nonzero RationalOrder

end OriginalPrimeThreeLocalOrderNormal318
