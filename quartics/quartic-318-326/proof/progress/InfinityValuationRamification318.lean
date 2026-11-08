module
public import InfinityReciprocalRamification318
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public section
noncomputable section
namespace InfinityValuationRamification318
open Polynomial InfinityReciprocalAction318 IsDedekindDomain
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDedekind:IsDedekindDomain (Order c):=InfinityBranchValuation318.order_dedekind c
local instance baseDedekind:IsDedekindDomain (Base c):=InfinityReciprocalPrime318.base_dedekind c
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
local instance orderAlgebra:Algebra (Order c) (L c):=(InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance orderFraction:IsFractionRing (Order c) (L c):=InfinityOpenFractionField318.open_fractionField c
local instance reciprocalAlgebra:Algebra (Base c) (L c):=(ReciprocalInfinityNormalization318.reciprocalEmbedding c).toAlgebra
local instance reciprocalSMul:SMul (Base c) (L c):=(reciprocalAlgebra c).toSMul
local instance reciprocalModule:Module (Base c) (L c):=Algebra.toModule
local instance originalTower:IsScalarTower (Base c) (Order c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=Base c) (S:=Order c) (A:=L c) (fun _=>rfl)
local instance fieldBase:Algebra (Base c) K:=ReciprocalBaseFraction318.baseAlgebra c
local instance fieldFraction:IsFractionRing (Base c) K:=ReciprocalBaseFraction318.actual_fractionField c
local instance fieldTower:IsScalarTower (Base c) K (L c):=
  IsScalarTower.of_algebraMap_eq (fun x=>(ReciprocalBaseFraction318.original_field_value c x).symm)
local instance orderTorsionFree:Module.IsTorsionFree (Base c) (Order c):=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (InfinityOrderGalois318.chart_injective c)
lemma base_prime_ne_bot:InfinityReciprocalPrime318.prime c≠⊥:=by
  intro h
  have hz:=InfinityReciprocalPrime318.coordinate_mem c
  rw [h,Ideal.mem_bot] at hz
  have hh:=congrArg (ReciprocalBaseFraction318.baseFieldMap c) hz
  rw [ReciprocalBaseFraction318.on_coordinate,map_zero] at hh
  exact (inv_ne_zero RatFunc.X_ne_zero) hh
/-- The actual rational infinity place of the reciprocal base. -/
@[expose] def basePlace:HeightOneSpectrum (Base c):=
  ⟨InfinityReciprocalPrime318.prime c,(InfinityReciprocalPrime318.maximal c).isPrime,base_prime_ne_bot c⟩
variable (Q:Ideal (Order c)) [Q.IsPrime]
variable (hs:InfinityPrimeSignInertia318.reciprocalCoordinate c∈Q)
/-- The normalized adic valuation restriction in the same original fields:
every base value is squared, including zero. This uses the proved index,
not an inference from inertia cardinality alone. -/
theorem valuation_restriction (x:K):
    (basePlace c).valuation K x ^ 2=
      (InfinityBranchValuation318.place c Q hs).valuation (L c) (algebraMap K (L c) x):=by
  letI:(InfinityBranchValuation318.place c Q hs).asIdeal.LiesOver (basePlace c).asIdeal:=
    InfinityReciprocalPrime318.liesOver c Q hs
  have hh:=HeightOneSpectrum.valuation_liesOver (L c) (basePlace c)
    (InfinityBranchValuation318.place c Q hs) x
  rw [InfinityBranchValuation318.place_ideal,InfinityReciprocalRamification318.ramificationIdx_two c Q hs] at hh
  exact hh
end InfinityValuationRamification318
