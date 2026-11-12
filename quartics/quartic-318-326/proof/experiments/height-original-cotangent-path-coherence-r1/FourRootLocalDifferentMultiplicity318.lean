module
public import FourRootActualInfinityTraceTransport318
public section
noncomputable section
namespace ActualLocalIdealMultiplicity318
open IsDiscreteValuationRing Submodule.IsPrincipal
variable (R:Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
/-- Normalized local coefficient of the ACTUAL ideal, not an indicator
introduced from a previously desired support. -/
@[expose] def coefficient(J:Ideal R):ℕ:=(addVal R (generator J)).toNat
lemma coefficient_top:coefficient R ⊤=0:=by
  have hu:IsUnit (generator (⊤:Ideal R)):=Ideal.span_singleton_eq_top.mp
    (Ideal.span_singleton_generator _)
  simp only [coefficient,addVal_eq_zero_iff.mpr hu,ENat.toNat_zero]
lemma coefficient_uniformizer(J:Ideal R)(z:R)(hz:Irreducible z)(hJ:J=Ideal.span {z}):
    coefficient R J=1:=by
  have ha:Associated (generator J) z:=by
    rw [hJ]
    exact associated_generator_span_self _
  have hv: addVal R z=1:=addVal_def _ 1 hz 1 (by simp)
  have he:=(addVal_eq_iff_associated _ _).mpr ha
  simp only [coefficient,he,hv,ENat.toNat_one]
end ActualLocalIdealMultiplicity318

namespace FourRootLocalDifferentMultiplicity318
open Polynomial FourRootActualFractionField318 FourRootActualFiniteBranchChart318
open FourRootActualResidueInertia318 FourRootNormalizedPointCharts318
open FourRootActualLocalTraceDifferent318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance affineFinite:Module.Finite ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).1
local instance affineFree:Module.Free ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).2
local instance pointPrime(p:FinitePoints b):(finitePrime b p).IsPrime:=finite_prime b p
lemma all_finite_prime_nonzero(p:FinitePoints b):finitePrime b p≠⊥:=by
  intro he
  have hm:algebraMap ℂ[X] (A b) (X-C p.val.1)∈finitePrime b p:=by
    change finiteEvaluation b p _=0
    rw [FourRootActualKaehlerNeighborhoods318.finite_eval_polynomial]
    simp
  rw [he,Ideal.mem_bot] at hm
  have hi:Function.Injective (algebraMap ℂ[X] (A b)):=FaithfulSMul.algebraMap_injective _ _
  exact Polynomial.X_sub_C_ne_zero _ (hi (by simpa only [map_zero] using hm))
local instance finiteDvr(p:FinitePoints b):IsDiscreteValuationRing (Stalk b p):=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (A b) (all_finite_prime_nonzero b hb p) (Stalk b p)
@[expose] def finiteCoefficient(p:FinitePoints b):ℕ:=
  ActualLocalIdealMultiplicity318.coefficient (Stalk b p) (traceAt b hb p)
lemma finite_branch(p:FinitePoints b)(i:Fin 4)(hp:p.val.1=b i):finiteCoefficient b hb p=1:=
  ActualLocalIdealMultiplicity318.coefficient_uniformizer _ _ _
    (FourRootActualLocalUniformizer318.actual_uniformizer b hb i p hp)
    (FourRootActualLocalTraceDifferent318.at_actual_branch b hb p i hp)
lemma finite_regular(p:FinitePoints b)(hp:∀i,p.val.1≠b i):finiteCoefficient b hb p=0:=by
  have hn:¬finitePrime b p∣differentIdeal ℂ[X] (A b):=by
    have h:=FourRootActualTraceDifferentSupport318.actual_trace_support b hb p
    change (finitePrime b p∣differentIdeal ℂ[X] (A b))↔_ at h
    exact fun hd=>by obtain ⟨i,hi⟩:=h.mp hd;exact hp i hi
  have ht:traceAt b hb p=⊤:=ideal_unit_at b hb p _ hn
  rw [finiteCoefficient,ht,ActualLocalIdealMultiplicity318.coefficient_top]
theorem finite_exact(p:FinitePoints b):
    finiteCoefficient b hb p=if ∃i,p.val.1=b i then 1 else 0:=by
  classical
  by_cases hp:∃i,p.val.1=b i
  · obtain ⟨i,hi⟩:=hp
    rw [if_pos ⟨i,hi⟩]
    exact finite_branch b hb p i hi
  · rw [if_neg hp]
    exact finite_regular b hb p (by simpa only [not_exists] using hp)
end FourRootLocalDifferentMultiplicity318

namespace FourRootInfinityDifferentMultiplicity318
open Polynomial FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualInfinityTraceTransport318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance reciprocalBase:Algebra ℂ[X] (I b):=
  (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2)).toAlgebra
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
local instance infinityFree:Module.Free ℂ[X] (I b):=(FourRootSquaredInfinityBase318.finite_free b).2
local instance pointPrime(p:InfinityPoints b):(infinityPrime b p).IsPrime:=infinity_prime b p
lemma center_prime_nonzero(p:InfinityPoints b)(hp:p.val.1=0):infinityPrime b p≠⊥:=by
  intro he
  have hm:algebraMap ℂ[X] (I b) X∈infinityPrime b p:=by
    change infinityEvaluation b p (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2) X)=0
    rw [Polynomial.aeval_X,map_pow]
    change p.val.1^2=0
    rw [hp,zero_pow (by decide:2≠0)]
  rw [he,Ideal.mem_bot] at hm
  have hi:Function.Injective (algebraMap ℂ[X] (I b)):=FaithfulSMul.algebraMap_injective _ _
  exact Polynomial.X_ne_zero (hi (by simpa only [map_zero] using hm))
lemma local_dvr(p:InfinityPoints b)(hp:p.val.1=0):IsDiscreteValuationRing (Stalk b p):=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (I b) (center_prime_nonzero b hb p hp) (Stalk b p)
@[expose] def coefficient(p:InfinityPoints b)(hp:p.val.1=0):ℕ:=
  letI:=local_dvr b hb p hp
  ActualLocalIdealMultiplicity318.coefficient (Stalk b p) (traceAt b hb p)
/-- Each of the eight original reciprocal-chart centers contributes
ONE true trace-different coefficient, not merely index-two evidence. -/
theorem coefficient_one(p:InfinityPoints b)(hp:p.val.1=0):coefficient b hb p hp=1:=by
  letI:=local_dvr b hb p hp
  exact ActualLocalIdealMultiplicity318.coefficient_uniformizer _ _ _
    (actual_infinity_uniformizer b hb p hp) (actual_infinity_trace b hb p hp)
end FourRootInfinityDifferentMultiplicity318
