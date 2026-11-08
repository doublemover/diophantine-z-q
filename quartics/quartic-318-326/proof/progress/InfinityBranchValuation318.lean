module
public import InfinityPrimeSignInertia318
public import InfinityNormalChart318
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public section
noncomputable section
namespace InfinityBranchValuation318
open Polynomial IsDedekindDomain InfinityReciprocalAction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDomain:IsDomain (Order c):=InfinityOpenChart318.openOrder_domain c
local instance orderAlgebra:Algebra (Order c) (L c):=(InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance orderFraction:IsFractionRing (Order c) (L c):=InfinityOpenFractionField318.open_fractionField c
/-- Dedekindness of the entire actual infinity order. The u-line is used
only for this ring property, not as the original unramified base. -/
theorem order_dedekind:IsDedekindDomain (Order c):=by
  letI:=InfinityNormalChart318.open_integrallyClosed c
  letI:Module.Finite (InfinityOpenChart318.OpenBase c) (Order c):=
    (InfinityOpenChart318.finite_free_etale_rank_eight c).1
  letI:IsNoetherianRing (Order c):=IsNoetherianRing.of_finite (InfinityOpenChart318.OpenBase c) (Order c)
  letI:Algebra.IsIntegral (InfinityOpenChart318.OpenBase c) (Order c):=
    Algebra.IsIntegral.of_finite _ _
  letI:Ring.DimensionLEOne (InfinityOpenChart318.OpenBase c):=
    Ring.DimensionLEOne.localization (R:=ℚ[X]) (M:=Submonoid.powers (InfinityOpenChart318.denominator c)) (InfinityOpenChart318.OpenBase c) (by
      rintro _ ⟨n,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (InfinityOpenChart318.denominator_ne_zero c)))
  letI:Ring.DimensionLEOne (Order c):=Ring.DimensionLEOne.of_isIntegral (InfinityOpenChart318.OpenBase c) (Order c)
  exact { (inferInstance:IsDomain (Order c)), (inferInstance:IsNoetherianRing (Order c)),
    (inferInstance:Ring.DimensionLEOne (Order c)), (inferInstance:IsIntegrallyClosed (Order c)) with }
local instance orderDedekind:IsDedekindDomain (Order c):=order_dedekind c

lemma reciprocal_ne_zero:InfinityPrimeSignInertia318.reciprocalCoordinate c≠0:=by
  intro h
  have hh:=congrArg (InfinityOpenFractionField318.openEmbedding c) h
  have he:InfinityOpenFractionField318.openEmbedding c
      (InfinityPrimeSignInertia318.reciprocalCoordinate c)=
      (algebraMap K (L c) RatFunc.X)⁻¹:=by
    exact ReciprocalInfinityNormalization318.reciprocalEmbedding_coordinate c
  rw [he,map_zero] at hh
  have hx:algebraMap K (L c) RatFunc.X≠0:=
    by simpa only [map_zero] using (RingHom.injective (algebraMap K (L c))).ne RatFunc.X_ne_zero
  exact (inv_ne_zero hx) hh
variable (Q:Ideal (Order c)) [Q.IsPrime]
variable (hs:InfinityPrimeSignInertia318.reciprocalCoordinate c∈Q)
include hs
lemma prime_ne_bot:Q≠⊥:=by
  intro h
  exact reciprocal_ne_zero c (by simpa only [h,Ideal.mem_bot] using hs)
/-- The supplied prime itself is the place, in the original whole field. -/
@[expose] def place:HeightOneSpectrum (Order c):=⟨Q,inferInstance,prime_ne_bot c Q hs⟩
@[simp] theorem place_ideal:(place c Q hs).asIdeal=Q:=rfl
@[expose] abbrev valuationRing:ValuationSubring (L c):=
  HeightOneSpectrum.valuationSubringAtPrime (L c) (place c Q hs)
theorem actual_localization:IsLocalization Q.primeCompl (valuationRing c Q hs):=by
  change IsLocalization (place c Q hs).asIdeal.primeCompl
    (HeightOneSpectrum.valuationSubringAtPrime (L c) (place c Q hs))
  infer_instance
theorem equals_adic_valuation:valuationRing c Q hs=
    ((place c Q hs).valuation (L c)).valuationSubring:=
  HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (place c Q hs)
end InfinityBranchValuation318
