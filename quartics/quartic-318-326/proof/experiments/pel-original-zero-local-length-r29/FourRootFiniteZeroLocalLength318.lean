module
public import FourRootAllPrimeFiniteDifferent318
public import FourRootLocalDifferentMultiplicity318
public import Mathlib.RingTheory.Length
public section
noncomputable section
namespace FourRootFiniteZeroLocalLength318
open Polynomial FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualFractionField318 FourRootActualLocalTraceDifferent318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=
  FourRootActualDedekind318.finite_dedekind b hb
local instance affineFree:Module.Free ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).2
local instance pointPrime(p:FinitePoints b):(finitePrime b p).IsPrime:=finite_prime b p
/-- Restriction of the ORIGINAL whole derivative-zero ideal to the
actual local ring. No reduced ideal or pointwise substitute is used. -/
@[expose] def zeroAt(p:FinitePoints b):Ideal (Stalk b p):=
  (FourRootDerivativeZeroIdeals318.finiteIdeal b).map (algebraMap (A b) (Stalk b p))
lemma zero_eq_trace(p:FinitePoints b):zeroAt b p=traceAt b hb p:=by
  rw [zeroAt,←FourRootAllPrimeFiniteDifferent318.trace_equals_zero_ideal b hb]
  rfl
lemma branch_maximal(p:FinitePoints b)(i:Fin 4)(hp:p.val.1=b i):
    zeroAt b p=IsLocalRing.maximalIdeal (Stalk b p):=by
  rw [zero_eq_trace b hb p]
  exact FourRootActualLocalUniformizer318.trace_eq_maximal b hb i p hp
lemma regular_top(p:FinitePoints b)(hp:∀i,p.val.1≠b i):zeroAt b p=⊤:=by
  rw [zero_eq_trace b hb p]
  apply FourRootActualLocalTraceDifferent318.ideal_unit_at b hb p
  intro hd
  have h:=FourRootActualTraceDifferentSupport318.actual_trace_support b hb p
  change (finitePrime b p∣differentIdeal ℂ[X] (A b))↔_ at h
  obtain ⟨i,hi⟩:=h.mp hd
  exact hp i hi
/-- Length of the actual local quotient module, not valuation of a
chosen generator. It can now be compared with the earlier different
coefficient without identifying the two by definition. -/
@[expose] def localLength(p:FinitePoints b):ℕ∞:=
  Module.length (Stalk b p) ((Stalk b p)⧸zeroAt b p)
theorem branch_length(p:FinitePoints b)(i:Fin 4)(hp:p.val.1=b i):localLength b p=1:=by
  letI:IsDiscreteValuationRing (Stalk b p):=
    FourRootActualLocalUniformizer318.local_dvr b hb i p hp
  rw [localLength,branch_maximal b hb p i hp]
  simpa only [pow_one,Nat.cast_one] using
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (Stalk b p) 1
theorem regular_length(p:FinitePoints b)(hp:∀i,p.val.1≠b i):localLength b p=0:=by
  rw [localLength,regular_top b hb p hp]
  exact Module.length_eq_zero _ _
theorem exact_length(p:FinitePoints b):
    localLength b p=if ∃i,p.val.1=b i then 1 else 0:=by
  classical
  by_cases hp:∃i,p.val.1=b i
  · obtain ⟨i,hi⟩:=hp
    rw [if_pos ⟨i,hi⟩]
    exact branch_length b hb p i hi
  · rw [if_neg hp]
    exact regular_length b hb p (by simpa only [not_exists] using hp)
/-- Every complex-point local quotient is reduced. Whole-scheme
reducedness still requires covering ALL scheme primes, not just these
complex points. -/
theorem local_reduced(p:FinitePoints b):IsReduced ((Stalk b p)⧸zeroAt b p):=by
  classical
  by_cases hp:∃i,p.val.1=b i
  · obtain ⟨i,hi⟩:=hp
    rw [branch_maximal b hb p i hi]
    infer_instance
  · rw [regular_top b hb p (by simpa only [not_exists] using hp)]
    infer_instance
end FourRootFiniteZeroLocalLength318
