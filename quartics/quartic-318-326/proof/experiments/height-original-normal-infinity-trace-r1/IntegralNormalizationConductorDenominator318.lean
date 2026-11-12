module
public import FiniteFrameConductorDenominator318
public import IntegralFourRootNormalizationConductor318
public import LocalizedNormalModel318
public section
noncomputable section
namespace IntegralNormalizationConductorDenominator318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
@[expose] def denominator : P :=
  IntegralReciprocalBase318.finiteDenominator R a (arithmeticDenominator R d)

include hd in
/-- Finiteness of the actual normalization and the original marked
basis produce ONE arithmetic denominator power inside the whole conductor.
No nonzero-conductor or common-denominator premise is supplied. -/
theorem exists_power : ∃ n : ℕ,(algebraMap P B (denominator R a d))^n ∈
    IntegralFourRootNormalizationConductor318.conductor R a d := by
  letI : Module.Finite F B := (finite_free_etale R a d).1
  letI : Algebra.Etale F B := (finite_free_etale R a d).2.2
  have hden : denominator R a d ≠ 0 :=
    IntegralReciprocalBase318.finiteDenominator_ne_zero R a _
      (arithmeticDenominator_ne_zero R d hd)
  letI : Module.Finite P (IntegralFourRootNormalizationConductor318.normalOrder R a d) :=
    (LocalizedNormalModel318.finite_normal_model (Rf:=F) (B:=B)
      (denominator R a d) hden).1
  obtain ⟨r,hr⟩ := FiniteFrameConductorDenominator318.exists_denominator
    (Submonoid.powers (denominator R a d))
    (IntegralFourRootNormalizationConductor318.inclusion R a d)
    (FourRootIntegralDuality318.frame (DistinctContactIntegralDomain318.coefficient R a d)).basis
    (FourRootIntegralDuality318.frame
      (fun i => algebraMap P F (DistinctContactIntegralDomain318.coefficient R a d i))).basis
    (FourRootDualityBaseChange318.coefficientMap_basis _)
    (IntegralFourRootNormalizationConductor318.normalOrder R a d)
  obtain ⟨n,hn⟩ := r.property
  refine ⟨n,?_⟩
  simpa only [←hn,map_pow] using hr

lemma denominator_isUnit : IsUnit (algebraMap P B (denominator R a d)) := by
  rw [IsScalarTower.algebraMap_apply P F B]
  exact (IsLocalization.Away.algebraMap_isUnit (S:=F) (denominator R a d)).map
    (algebraMap F B)
end IntegralNormalizationConductorDenominator318
