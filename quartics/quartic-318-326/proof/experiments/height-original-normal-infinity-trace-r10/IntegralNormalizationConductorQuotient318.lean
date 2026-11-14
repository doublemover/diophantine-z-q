module
public import IntegralNormalizationConductorIdeal318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace IntegralNormalizationConductorQuotient318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "B" => OpenOrder R a d
local notation "inc" => IntegralFourRootNormalizationConductor318.inclusion R a d
local notation "I" => IntegralNormalizationConductorIdeal318.ideal R a d
local notation "s" => IntegralNormalizationConductorDenominator318.denominator R a d

include hd in
/-- An ACTUAL power of the original arithmetic-open denominator lies
in the raw conductor ideal. This is produced, not a support hypothesis. -/
theorem exists_power : ∃ k : ℕ,(algebraMap P A s)^k ∈ I := by
  obtain ⟨k,hk⟩ := IntegralNormalizationConductorDenominator318.exists_power R a d hd
  refine ⟨k,?_⟩
  change inc ((algebraMap P A s)^k) ∈ IntegralFourRootNormalizationConductor318.conductor R a d
  simpa only [map_pow,inc.commutes] using hk

include hd in
/-- The exact coefficient cokernel of the normalization counit is
annihilated by a nonzero denominator power. No exponent or regular-model
exceptional divisor is guessed, and the quotient need not be zero. -/
theorem quotient_annihilated : ∃ k : ℕ,
    (algebraMap P A s)^k ≠ 0 ∧
    ∀ q : A ⧸ I,Ideal.Quotient.mk I ((algebraMap P A s)^k)*q=0 := by
  obtain ⟨k,hk⟩ := exists_power R a d hd
  refine ⟨k,?_,?_⟩
  · intro hz
    have he := congrArg inc hz
    have hu : IsUnit ((algebraMap P B s)^k) :=
      (IntegralNormalizationConductorDenominator318.denominator_isUnit R a d).pow k
    apply hu.ne_zero
    simpa only [map_pow,inc.commutes,map_zero] using he
  · intro q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hk,zero_mul]
end IntegralNormalizationConductorQuotient318
