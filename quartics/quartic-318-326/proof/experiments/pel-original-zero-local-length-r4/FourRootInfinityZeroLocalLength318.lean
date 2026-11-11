module
public import FourRootWholeInfinityDifferent318
public import FourRootLocalDifferentMultiplicity318
public import Mathlib.RingTheory.Length
public section
noncomputable section
namespace FourRootInfinityZeroLocalLength318
open Polynomial FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualInfinityTraceTransport318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance reciprocalBase:Algebra ℂ[X] (I b):=
  (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2)).toAlgebra
local instance infinityDedekind:IsDedekindDomain (I b):=
  FourRootActualDedekind318.infinity_dedekind b hb
local instance infinityFree:Module.Free ℂ[X] (I b):=(FourRootSquaredInfinityBase318.finite_free b).2
local instance pointPrime(p:InfinityPoints b):(infinityPrime b p).IsPrime:=infinity_prime b p
@[expose] def zeroAt(p:InfinityPoints b):Ideal (Stalk b p):=
  (FourRootDerivativeZeroIdeals318.infinityIdeal b).map (algebraMap (I b) (Stalk b p))
lemma zero_eq_trace(p:InfinityPoints b):zeroAt b p=traceAt b hb p:=by
  rw [zeroAt,←FourRootWholeInfinityDifferent318.trace_equals_zero_ideal b hb]
  rfl
/-- The entire original infinity ideal is simple at every one of the
eight centers, over the SAME reciprocal base v=u². -/
lemma center_maximal(p:InfinityPoints b)(hp:p.val.1=0):
    zeroAt b p=IsLocalRing.maximalIdeal (Stalk b p):=by
  letI:IsDiscreteValuationRing (Stalk b p):=
    FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  rw [zero_eq_trace b hb p,actual_infinity_trace b hb p hp]
  exact (actual_infinity_uniformizer b hb p hp).maximalIdeal_eq.symm
@[expose] def localLength(p:InfinityPoints b):ℕ∞:=
  Module.length (Stalk b p) ((Stalk b p)⧸zeroAt b p)
theorem center_length(p:InfinityPoints b)(hp:p.val.1=0):localLength b p=1:=by
  letI:IsDiscreteValuationRing (Stalk b p):=
    FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  rw [localLength,center_maximal b hb p hp]
  simpa only [pow_one,Nat.cast_one] using
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (Stalk b p) 1
theorem center_reduced(p:InfinityPoints b)(hp:p.val.1=0):
    IsReduced ((Stalk b p)⧸zeroAt b p):=by
  rw [center_maximal b hb p hp]
  infer_instance
end FourRootInfinityZeroLocalLength318
