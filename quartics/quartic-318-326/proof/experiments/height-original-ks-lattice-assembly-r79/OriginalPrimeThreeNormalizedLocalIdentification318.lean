module
public import OriginalPrimeThreeLocalOrderNormal318
public import OriginalIntegerNormalizationMap318
public section
noncomputable section
namespace OriginalPrimeThreeNormalizedLocalIdentification318
open OriginalPrimeThreeLocalOrderQuotient318 OriginalPrimeThreeRationalLocalization318
open OriginalPrimeThreeLocalOrderNormal318
abbrev Closure := OriginalIntegerFiniteClosure318.Closure twist
local instance sourceField : Field L :=
  (KummerTensorField318.source_raw_field twist).toField
attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra
attribute [local instance] OriginalIntegerFractionField318.integerFieldAlgebra
attribute [local instance] OriginalIntegerNormalizationMap318.closureAlgebra
attribute [local instance] OriginalPrimeThreeLocalOrderNormal318.fieldAlgebra
local instance localFraction : IsFractionRing LocalOrder L := local_fractionField
local instance localNormal : IsIntegrallyClosed LocalOrder := localOrder_normal

local instance localSelfClosure : IsIntegralClosure LocalOrder LocalOrder L where
  algebraMap_injective := IsFractionRing.injective LocalOrder L
  isIntegral_iff := by
    intro x
    constructor
    · exact (isIntegrallyClosed_iff L).mp localNormal
    · rintro ⟨y, rfl⟩
      exact isIntegral_algebraMap

@[expose] def localClosureEquiv : integralClosure LocalOrder L ≃ₐ[LocalOrder] LocalOrder :=
  IsIntegralClosure.equiv LocalOrder (integralClosure LocalOrder L) L LocalOrder

/-- Every element of the ACTUAL normalized chart is integral over the
localized original order in the same original field. -/
@[expose] def intoLocalClosure : Closure →+* integralClosure LocalOrder L where
  toFun z := ⟨z.val, ((OriginalIntegerNormalizationMap318.integral_iff twist z.val).mpr
    z.property).tower_top⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[expose] def closureToLocal : Closure →+* LocalOrder :=
  localClosureEquiv.toRingHom.comp intoLocalClosure

theorem closureToLocal_val (z : Closure) :
    algebraMap LocalOrder L (closureToLocal z) = z.val :=
  IsIntegralClosure.algebraMap_equiv LocalOrder (integralClosure LocalOrder L)
    L LocalOrder (intoLocalClosure z)

theorem closureToLocal_injective : Function.Injective closureToLocal := by
  intro x y h
  apply Subtype.ext
  simpa only [closureToLocal_val] using congrArg (algebraMap LocalOrder L) h

theorem closureToLocal_on_order (a : Order) :
    closureToLocal (algebraMap Order Closure a) = algebraMap Order LocalOrder a := by
  apply IsFractionRing.injective LocalOrder L
  rw [closureToLocal_val, ← IsScalarTower.algebraMap_apply Order LocalOrder L]
  rfl

@[expose] def closureLocalAlgebra : Algebra Closure LocalOrder := closureToLocal.toAlgebra
attribute [local instance] closureLocalAlgebra
abbrev closureDenominators : Submonoid Closure :=
  Algebra.algebraMapSubmonoid Closure denominators

/-- The image submonoid is exactly the prime-to-three INTEGER coefficient
set on the actual normalized chart; no root or parameter is inverted. -/
theorem closureDenominators_eq_integer : closureDenominators =
    Algebra.algebraMapSubmonoid Closure
      PrimeThreeCoefficientLocalization318.primeIdeal.primeCompl := by
  ext z
  constructor
  · rintro ⟨a, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, by simp only [map_intCast]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨algebraMap ℤ Order n, ⟨n, hn, rfl⟩, by simp only [map_intCast]⟩

/-- This is the whole coefficient localization of the actual normalized
chart. Surjectivity of fractions comes from the ORIGINAL order inside it,
not from an assumed equality of normalizations. -/
theorem actual_normalized_localization : IsLocalization closureDenominators LocalOrder := by
  apply (isLocalization_iff closureDenominators LocalOrder).mpr
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨z, a, ha, rfl⟩
    change IsUnit (closureToLocal (algebraMap Order Closure a))
    rw [closureToLocal_on_order]
    exact IsLocalization.map_units LocalOrder ⟨a, ha⟩
  · intro z
    obtain ⟨⟨a, m⟩, he⟩ := IsLocalization.surj denominators z
    refine ⟨⟨algebraMap Order Closure a,
      ⟨algebraMap Order Closure m, ⟨m, m.property, rfl⟩⟩⟩, ?_⟩
    change z * closureToLocal (algebraMap Order Closure m) =
      closureToLocal (algebraMap Order Closure a)
    simpa only [closureToLocal_on_order] using he
  · intro x y h
    exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using closureToLocal_injective h⟩

/-- A concrete localization of the ACTUAL normalized finite chart is the
actual normal Z_(3) order, preserving its exact chart inclusion. -/
@[expose] def normalizedLocalEquiv : Localization closureDenominators ≃ₐ[Closure] LocalOrder := by
  letI := actual_normalized_localization
  exact IsLocalization.algEquiv closureDenominators
    (Localization closureDenominators) LocalOrder

theorem normalizedLocalEquiv_on_chart (z : Closure) :
    normalizedLocalEquiv (algebraMap Closure (Localization closureDenominators) z) =
      closureToLocal z := normalizedLocalEquiv.commutes z

end OriginalPrimeThreeNormalizedLocalIdentification318
