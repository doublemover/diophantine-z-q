module
public import InfinityOrderInertia318
public import ReciprocalBaseFraction318
public section
noncomputable section
namespace InfinityReciprocalRamification318
open InfinityReciprocalAction318
set_option maxHeartbeats 550000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDomain:IsDomain (Order c):=InfinityOpenChart318.openOrder_domain c
local instance baseDomain:IsDomain (Base c):=
  Localization.Away.isDomain (ReciprocalInfinityBase318.reciprocalDenominator_ne_zero c)
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
local instance reciprocalAlgebra:Algebra (Base c) (L c):=(ReciprocalInfinityNormalization318.reciprocalEmbedding c).toAlgebra
local instance reciprocalSMul:SMul (Base c) (L c):=(reciprocalAlgebra c).toSMul
local instance reciprocalModule:Module (Base c) (L c):=Algebra.toModule
local instance fieldBase:Algebra (Base c) K:=ReciprocalBaseFraction318.baseAlgebra c
local instance fieldFraction:IsFractionRing (Base c) K:=ReciprocalBaseFraction318.actual_fractionField c
local instance fieldTower:IsScalarTower (Base c) K (L c):=
  IsScalarTower.of_algebraMap_eq (fun x=>(ReciprocalBaseFraction318.original_field_value c x).symm)
local instance orderFinite:Module.Finite (Base c) (Order c):=(InfinityOrderGalois318.finite_flat c).1
local instance orderFlat:Module.Flat (Base c) (Order c):=(InfinityOrderGalois318.finite_flat c).2
local instance groupFinite:Finite (InfinityOrderGalois318.G c):=InfinityOrderGalois318.group_finite c
local instance groupGalois:IsGaloisGroup (InfinityOrderGalois318.G c) (Base c) (Order c):=
  InfinityOrderGalois318.galoisGroup c
local instance basePrime:(InfinityReciprocalPrime318.prime c).IsPrime:=(InfinityReciprocalPrime318.maximal c).isPrime
local instance separableResidue:Algebra.HasSeparableResidueFieldsAt (Base c) (Order c)
    (InfinityReciprocalPrime318.prime c):=InfinityReciprocalPrime318.residue_separable c
variable (Q:Ideal (Order c)) [Q.IsPrime]
variable (hs:InfinityPrimeSignInertia318.reciprocalCoordinate c∈Q)
include hs in
/-- The actual original reciprocal-base ramification index, obtained from
full Galois invariants, finite flatness, and separable residue fields. -/
theorem ramificationIdxIn_two:
    Ideal.ramificationIdxIn (InfinityReciprocalPrime318.prime c) (Order c)=2:=by
  letI:Q.LiesOver (InfinityReciprocalPrime318.prime c):=InfinityReciprocalPrime318.liesOver c Q hs
  have hh:=Ideal.card_inertia_eq_ramificationIdxIn
    (G:=InfinityOrderGalois318.G c) (InfinityReciprocalPrime318.prime c) Q
  exact hh.symm.trans (InfinityOrderInertia318.ideal_inertia_card c Q hs)
include hs in
theorem ramificationIdx_two:Q.ramificationIdx (Base c)=2:=by
  letI:Q.LiesOver (InfinityReciprocalPrime318.prime c):=InfinityReciprocalPrime318.liesOver c Q hs
  rw [←Ideal.ramificationIdxIn_eq_ramificationIdx (InfinityReciprocalPrime318.prime c) Q
    (InfinityOrderGalois318.G c)]
  exact ramificationIdxIn_two c Q hs

local instance orderIntegral:Algebra.IsIntegral (Base c) (Order c):=Algebra.IsIntegral.of_finite _ _
local instance orderFaithful:FaithfulSMul (Base c) (Order c):=
  (faithfulSMul_iff_algebraMap_injective (Base c) (Order c)).mpr (InfinityOrderGalois318.chart_injective c)
/-- Infinity has actual primes above it in the whole order. -/
theorem primes_nonempty:Nonempty ((InfinityReciprocalPrime318.prime c).primesOver (Order c)):=inferInstance
/-- No prime or chosen residue point is an extra hypothesis in the final index. -/
theorem infinity_index_two:Ideal.ramificationIdxIn (InfinityReciprocalPrime318.prime c) (Order c)=2:=by
  obtain ⟨q⟩:=primes_nonempty c
  apply ramificationIdxIn_two c q.val
  exact (Ideal.mem_of_liesOver q.val (InfinityReciprocalPrime318.prime c) _).mp
    (InfinityReciprocalPrime318.coordinate_mem c)
/-- Every actual prime over original projective infinity has index two. -/
theorem every_prime_index_two (q:(InfinityReciprocalPrime318.prime c).primesOver (Order c)):
    q.val.ramificationIdx (Base c)=2:=by
  apply ramificationIdx_two c q.val
  exact (Ideal.mem_of_liesOver q.val (InfinityReciprocalPrime318.prime c) _).mp
    (InfinityReciprocalPrime318.coordinate_mem c)
end InfinityReciprocalRamification318
