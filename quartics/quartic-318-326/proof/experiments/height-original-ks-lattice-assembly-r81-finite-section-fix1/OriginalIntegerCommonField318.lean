module
public import FourRootOrderLocalizationMaps318
public import OriginalIntegerReciprocalCharts318
public import OriginalIntegerReciprocalNormalization318
public import IntegralFourRootScalarMaps318
public section
noncomputable section
namespace OriginalIntegerCommonField318
open Polynomial

/-- Resolve the exact map/algebra conversion on symbolic four-root carriers,
prior to inserting the rational-unit twist expressions. -/
private theorem finite_localization_generic (R : Type*) [CommRing R]
    (d a : Fin 4 → R) :
    letI : Algebra (IntegralFourRootReciprocalCharts318.FiniteOrder d a)
        (IntegralFourRootOverlap318.CommonOrder R d a) :=
      (IntegralFourRootOverlap318.finiteMap R d a).toAlgebra
    IsLocalization.Away
      (algebraMap R[X] (IntegralFourRootReciprocalCharts318.FiniteOrder d a) X)
      (IntegralFourRootOverlap318.CommonOrder R d a) := by
  letI : Algebra (IntegralFourRootReciprocalCharts318.FiniteOrder d a)
      (IntegralFourRootOverlap318.CommonOrder R d a) :=
    (IntegralFourRootOverlap318.finiteMap R d a).toAlgebra
  exact FourRootOrderLocalizationMaps318.localization
    (A := R[X]) (T := IntegralWholeReciprocalOverlap318.Laurent R)
    (C := IntegralFourRootOverlap318.CommonOrder R d a)
    (IntegralFourRootReciprocalCharts318.finiteCoefficient d a)
    (RingEquiv.refl (IntegralFourRootOverlap318.CommonOrder R d a)) (X : R[X])

/-- Injectivity uses the same proved localization and the actual free-order
parameter regularity; no order-domain hypothesis is added. -/
private theorem finiteMap_injective_generic (R : Type*) [CommRing R] [IsDomain R]
    (d a : Fin 4 → R) : Function.Injective (IntegralFourRootOverlap318.finiteMap R d a) := by
  letI : Algebra (IntegralFourRootReciprocalCharts318.FiniteOrder d a)
      (IntegralFourRootOverlap318.CommonOrder R d a) :=
    (IntegralFourRootOverlap318.finiteMap R d a).toAlgebra
  letI := finite_localization_generic R d a
  exact IsLocalization.injective (IntegralFourRootOverlap318.CommonOrder R d a)
    (Submonoid.powers_le.mpr (FourRootOrderLocalizationMaps318.scalar_regular
      (IntegralFourRootReciprocalCharts318.finiteCoefficient d a) (X : R[X])
      Polynomial.X_ne_zero))

attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra
attribute [local instance] OriginalIntegerFractionField318.integerFieldAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.laurentAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev L := OriginalIntegerFiniteClosure318.L c
abbrev Laurent := IntegralWholeReciprocalOverlap318.Laurent ℤ
abbrev Order := OriginalIntegerAffineModel318.Order c
abbrev CommonOrder := IntegralFourRootOverlap318.CommonOrder ℤ
  (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- The existing finite-to-Laurent four-root map, with its original coefficients. -/
@[expose] def finiteMap : Order c →+* CommonOrder c :=
  IntegralFourRootOverlap318.finiteMap ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts
@[expose] def finiteAlgebra : Algebra (Order c) (CommonOrder c) :=
  (finiteMap c).toAlgebra
attribute [local instance] finiteAlgebra

/-- Only the actual parameter is inverted, not an integer or a root. -/
theorem finite_localization :
    IsLocalization.Away (algebraMap ℤ[X] (Order c) X) (CommonOrder c) := by
  exact finite_localization_generic ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

theorem finiteMap_injective : Function.Injective (finiteMap c) := by
  exact finiteMap_injective_generic ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

/-- The literal coefficient square for the existing finite chart map. -/
theorem finite_polynomial (p : ℤ[X]) :
    finiteMap c (algebraMap ℤ[X] (Order c) p) =
      algebraMap Laurent (CommonOrder c) (algebraMap ℤ[X] Laurent p) :=
  IntegralFourRootScalarMaps318.finite_polynomial ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts p

theorem parameter_unit : IsUnit
    (OriginalIntegerFractionField318.fieldEmbedding c (algebraMap ℤ[X] (Order c) X)) := by
  rw [OriginalIntegerNormalizationMap318.fieldEmbedding_on_polynomial]
  exact OriginalIntegerNormalizedOverlap318.parameterUnit c

/-- Extend the already injective integer-order embedding into the SAME original field. -/
@[expose] def fieldMap : CommonOrder c →+* L c := by
  letI := finite_localization c
  exact IsLocalization.Away.lift (S := CommonOrder c)
    (g := OriginalIntegerFractionField318.fieldEmbedding c) (algebraMap ℤ[X] (Order c) X) (parameter_unit c)

theorem fieldMap_on_finite (z : Order c) :
    fieldMap c (finiteMap c z) = OriginalIntegerFractionField318.fieldEmbedding c z := by
  letI := finite_localization c
  exact IsLocalization.Away.lift_eq (S := CommonOrder c)
    (g := OriginalIntegerFractionField318.fieldEmbedding c) (algebraMap ℤ[X] (Order c) X) (parameter_unit c) z

theorem fieldMap_injective : Function.Injective (fieldMap c) := by
  letI := finite_localization c
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (algebraMap ℤ[X] (Order c) X))]
  intro x y
  change finiteMap c x = finiteMap c y ↔
    fieldMap c (finiteMap c x) = fieldMap c (finiteMap c y)
  rw [fieldMap_on_finite, fieldMap_on_finite]
  exact (finiteMap_injective c).eq_iff.trans
    (OriginalIntegerFractionField318.fieldEmbedding_injective c).eq_iff.symm

@[expose] def fieldAlgebra : Algebra (CommonOrder c) (L c) := (fieldMap c).toAlgebra
attribute [local instance] fieldAlgebra

/-- Explicit projected actions of the three named algebra maps. -/
theorem field_scalar_tower : @IsScalarTower (Order c) (CommonOrder c) (L c)
    (finiteAlgebra c).toSMul (fieldAlgebra c).toSMul
    (OriginalIntegerFractionField318.integerFieldAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq (R := Order c) (S := CommonOrder c) (A := L c)
    (fun z => (fieldMap_on_finite c z).symm)

theorem common_domain : IsDomain (CommonOrder c) :=
  Function.Injective.isDomain (fieldMap c) (fieldMap_injective c)

/-- The common order has the original function field by the actual finite localization. -/
theorem actual_fractionField : IsFractionRing (CommonOrder c) (L c) := by
  letI := OriginalIntegerAffineModel318.order_domain c
  letI := finite_localization c
  letI := field_scalar_tower c
  letI := OriginalIntegerFractionField318.actual_fractionField c
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (algebraMap ℤ[X] (Order c) X)) (CommonOrder c) (L c)

/-- The extended map agrees with the already constructed finite Laurent action,
not an arbitrary embedding of the Laurent ring. -/
theorem fieldMap_on_laurent (a : Laurent) :
    fieldMap c (algebraMap Laurent (CommonOrder c) a) = algebraMap Laurent (L c) a := by
  have h : (fieldMap c).comp (algebraMap Laurent (CommonOrder c)) =
      algebraMap Laurent (L c) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X : ℤ[X]))
    apply RingHom.ext
    intro p
    change fieldMap c (algebraMap Laurent (CommonOrder c)
      (algebraMap ℤ[X] Laurent p)) = algebraMap Laurent (L c) (algebraMap ℤ[X] Laurent p)
    rw [← finite_polynomial, fieldMap_on_finite,
      OriginalIntegerNormalizationMap318.fieldEmbedding_on_polynomial]
    exact (IntegralClosureAwayField318.fieldMap_on_base (X : ℤ[X])
      (OriginalIntegerNormalizedOverlap318.parameterUnit c) p).symm
  exact RingHom.congr_fun h a

end OriginalIntegerCommonField318
