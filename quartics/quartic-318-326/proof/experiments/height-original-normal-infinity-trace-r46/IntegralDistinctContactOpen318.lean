module
public import DistinctContactIntegralDomain318
public import IntegralReciprocalBase318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace IntegralDistinctContactOpen318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
@[expose] def arithmeticDenominator : R := 2 * ∏ i : Fin 4, d i
abbrev Base := IntegralReciprocalBase318.FiniteBase R a (arithmeticDenominator R d)
abbrev Source := DistinctContactIntegralDomain318.Source R a d
abbrev OpenOrder := FourRootOrder318.Order
  (fun i => algebraMap R[X] (Base R a d) (DistinctContactIntegralDomain318.coefficient R a d i))

theorem constant_unit_of_dvd (r : R) (hr : r ∣ arithmeticDenominator R d) :
    IsUnit (algebraMap R (Base R a d) r) := by
  obtain ⟨q,hq⟩ := hr
  have h := IntegralReciprocalBase318.finite_constant_unit R a (arithmeticDenominator R d)
  change IsUnit (algebraMap R (Base R a d) (arithmeticDenominator R d)) at h
  rw [hq, map_mul] at h
  exact (isUnit_mul_iff.mp h).1

theorem two_unit : IsUnit (2 : Base R a d) := by
  simpa only [map_ofNat] using constant_unit_of_dvd R a d 2 (dvd_mul_right _ _)
theorem twist_unit (i : Fin 4) : IsUnit (algebraMap R (Base R a d) (d i)) :=
  constant_unit_of_dvd R a d (d i)
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _)
theorem coefficient_unit (i : Fin 4) :
    IsUnit (algebraMap R[X] (Base R a d) (DistinctContactIntegralDomain318.coefficient R a d i)) := by
  simpa only [DistinctContactIntegralDomain318.coefficient, map_mul, map_sub,
    IntegralReciprocalBase318.finite_C] using (twist_unit R a d i).mul
      (IntegralReciprocalBase318.finite_factor_unit R a (arithmeticDenominator R d) i)

/-- All four monic quadratic equations remain present. Their full source
becomes finite free and etale only on the stated arithmetic base open. -/
theorem finite_free_etale : Module.Finite (Base R a d) (OpenOrder R a d) ∧
    Module.Free (Base R a d) (OpenOrder R a d) ∧
    Algebra.Etale (Base R a d) (OpenOrder R a d) :=
  ⟨(FourRootOrder318.finite_free _).1, (FourRootOrder318.finite_free _).2,
    FourRootOrder318.etale _ (two_unit R a d) (coefficient_unit R a d)⟩

@[expose] def openBaseChange : Base R a d ⊗[R[X]] Source R a d ≃ₐ[Base R a d]
    OpenOrder R a d := FourRootOrder318.baseChange _ _

theorem arithmeticDenominator_ne_zero [IsDomain R] [CharZero R] (hd : ∀ i, d i ≠ 0) :
    arithmeticDenominator R d ≠ 0 :=
  mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))

theorem open_domain [IsDomain R] [CharZero R]
    (F : Type*) [Field F] [CharZero F] [Algebra R F]
    (hR : Function.Injective (algebraMap R F))
    (ha : Function.Injective a) (hd : ∀ i, d i ≠ 0) : IsDomain (OpenOrder R a d) := by
  let D := IntegralReciprocalBase318.finiteDenominator R a (arithmeticDenominator R d)
  have hD : D ≠ 0 := IntegralReciprocalBase318.finiteDenominator_ne_zero R a _
    (arithmeticDenominator_ne_zero R d hd)
  letI : IsDomain (Source R a d) :=
    DistinctContactIntegralDomain318.source_domain R F a d hR ha hd
  letI : Module.Free R[X] (Source R a d) := (FourRootOrder318.finite_free _).2
  have hi : Function.Injective (algebraMap R[X] (Source R a d)) :=
    FaithfulSMul.algebraMap_injective R[X] (Source R a d)
  have hD' : algebraMap R[X] (Source R a d) D ≠ 0 := by
    simpa only [map_zero] using hi.ne hD
  letI : IsLocalization.Away (algebraMap R[X] (Source R a d) D)
      (Source R a d ⊗[R[X]] Base R a d) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (Source R a d)
        (Submonoid.powers D)) (Source R a d ⊗[R[X]] Base R a d))
  letI : IsDomain (Source R a d ⊗[R[X]] Base R a d) :=
    IsLocalization.Away.isDomain _ hD'
  let e : OpenOrder R a d ≃+* (Source R a d ⊗[R[X]] Base R a d) :=
    (openBaseChange R a d).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm R[X] (Base R a d) (Source R a d)).toRingEquiv
  exact Function.Injective.isDomain e e.injective
end IntegralDistinctContactOpen318
