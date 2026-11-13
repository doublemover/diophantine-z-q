module
public import IntegralNormalizationConductorDenominator318
public import IntegralInfinityArithmeticDomain318
public section
noncomputable section
namespace IntegralNormalizationRawEmbedding318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  (a d : Fin 4 → R) (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "B" => OpenOrder R a d
local notation "F" => Base R a d

include hd in
/-- The SAME marked raw order embeds in its source open. Free tensor
base change and the actual nonzero denominator supply injection. -/
theorem inclusion_injective : Function.Injective
    (IntegralFourRootNormalizationConductor318.inclusion R a d) := by
  letI : Module.Free P A := (FourRootOrder318.finite_free _).2
  have hbase : Function.Injective (algebraMap P F) :=
    IntegralInfinityArithmeticDomain318.away_injective P F
      (IntegralNormalizationConductorDenominator318.denominator R a d)
      (IntegralReciprocalBase318.finiteDenominator_ne_zero R a _
        (arithmeticDenominator_ne_zero R d hd))
  exact (FourRootOrder318.baseChange (DistinctContactIntegralDomain318.coefficient R a d) F).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R:=P) (A:=F) (B:=A) hbase)

variable [IsNoetherianRing R] [IsIntegrallyClosed P] [IsDomain B]
include hd in
/-- A raw-order denominator is produced whose ambient image is a unit
and whose multiples of EVERY normal-order element lie in the raw order. -/
theorem exists_denominator : ∃ u : A,
    IsUnit (IntegralFourRootNormalizationConductor318.inclusion R a d u) ∧
    ∀ n : IntegralFourRootNormalizationConductor318.normalOrder R a d,
      ∃ v : A,IntegralFourRootNormalizationConductor318.inclusion R a d v =
        IntegralFourRootNormalizationConductor318.inclusion R a d u*n.val := by
  obtain ⟨k,hk⟩ := IntegralNormalizationConductorDenominator318.exists_power R a d hd
  let s := IntegralNormalizationConductorDenominator318.denominator R a d
  have he : IntegralFourRootNormalizationConductor318.inclusion R a d
      (algebraMap P A (s^k))=(algebraMap P B s)^k := by
    rw [AlgHom.commutes,map_pow]
  refine ⟨algebraMap P A (s^k),?_,?_⟩
  · rw [he]
    exact (IntegralNormalizationConductorDenominator318.denominator_isUnit R a d).pow k
  · rw [he]
    exact (FiniteOrderConductorTraceDual318.mem_conductor _ _ _).mp hk
end IntegralNormalizationRawEmbedding318
