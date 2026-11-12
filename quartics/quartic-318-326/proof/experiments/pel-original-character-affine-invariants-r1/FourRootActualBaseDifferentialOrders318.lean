module
public import ActualDvrMeromorphicOrder318
public import FourRootActualMeromorphicFrames318
public section
noncomputable section
namespace FourRootActualFiniteDifferentialOrders318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualFractionField318 FourRootActualFiniteBranchChart318
open FourRootActualLocalTraceDifferent318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance pointPrime(p:FinitePoints b):(finitePrime b p).IsPrime:=finite_prime b p
local instance finiteDvr(p:FinitePoints b):IsDiscreteValuationRing (Stalk b p):=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (A b) (FourRootLocalDifferentMultiplicity318.all_finite_prime_nonzero b hb p) (Stalk b p)
@[expose] def chartIndex(p:FinitePoints b):Fin 4:=
  if h:∃i,p.val.1=b i then Classical.choose h else 0
lemma chartIndex_branch(p:FinitePoints b)(j:Fin 4)(hp:p.val.1=b j):chartIndex b p=j:=by
  have h:∃i,p.val.1=b i:=⟨j,hp⟩
  rw [chartIndex,dif_pos h]
  apply hb
  exact (Classical.choose_spec h).symm.trans hp
lemma chartIndex_regular(p:FinitePoints b)(hp:∀i,p.val.1≠b i):chartIndex b p=0:=by
  rw [chartIndex,dif_neg (by simpa only [not_exists] using hp)]
/-- The chosen frame is genuinely defined on a principal neighborhood
of the SAME point; it is not an arbitrary meromorphic basis. -/
lemma chartIndex_neighborhood(p:FinitePoints b):denominator b (chartIndex b p)∉finitePrime b p:=by
  by_cases h:∃i,p.val.1=b i
  · obtain ⟨i,hi⟩:=h
    rw [chartIndex_branch b hb p i hi]
    exact FourRootActualKaehlerNeighborhoods318.finite_branch_neighborhood b hb p i hi
  · rw [chartIndex_regular b p (by simpa only [not_exists] using h)]
    change finiteEvaluation b p (denominator b 0)≠0
    rw [FourRootActualKaehlerNeighborhoods318.finite_eval_denominator]
    exact Finset.prod_ne_zero_iff.mpr (fun j _=>sub_ne_zero.mpr (fun he=>h ⟨_,he⟩))
/-- The coefficient is the actual original dt in its proved intrinsic
local frame, evaluated by the genuine normalized stalk DVR valuation. -/
@[expose] def coefficient(p:FinitePoints b):FourRootActualMeromorphicFinite318.F b:=
  FourRootActualMeromorphicFinite318.frame b hb (chartIndex b p)
    (KaehlerDifferential.D ℂ (FourRootActualMeromorphicFinite318.F b)
      (FourRootActualMeromorphicFinite318.t b))
@[expose] def value(p:FinitePoints b):WithTop ℤ:=
  ActualPrimeMeromorphicOrder318.value (A b) (finitePrime b p) (coefficient b hb p)
@[expose] def order(p:FinitePoints b):ℤ:=WithTop.untopD 0 (value b hb p)
lemma branch_value(p:FinitePoints b)(i:Fin 4)(hp:p.val.1=b i):value b hb p=1:=by
  rw [value,coefficient,chartIndex_branch b hb p i hp,
    FourRootActualMeromorphicFinite318.dt_coefficient,
    (ActualPrimeMeromorphicOrder318.value (A b) (finitePrime b p)).map_mul,
    ActualPrimeMeromorphicOrder318.value_two]
  have hz:=ActualPrimeMeromorphicOrder318.value_source_uniformizer (A b) (finitePrime b p)
    (FourRootAffineCoordinateRing318.coordinate b (some i))
    (FourRootActualLocalUniformizer318.actual_uniformizer b hb i p hp)
  change 0+ActualPrimeMeromorphicOrder318.value (A b) (finitePrime b p)
    (algebraMap (A b) (FractionRing (A b)) (FourRootAffineCoordinateRing318.coordinate b (some i)))=1
  rw [hz,zero_add]
lemma regular_value(p:FinitePoints b)(hp:∀i,p.val.1≠b i):value b hb p=0:=by
  rw [value,coefficient,FourRootActualMeromorphicFinite318.dt_coefficient,
    (ActualPrimeMeromorphicOrder318.value (A b) (finitePrime b p)).map_mul,
    ActualPrimeMeromorphicOrder318.value_two]
  have hn:FourRootAffineCoordinateRing318.coordinate b (some (chartIndex b p))∉finitePrime b p:=by
    change p.val.2 (chartIndex b p)≠0
    intro hz
    have hq:=p.property (chartIndex b p)
    rw [hz,zero_pow (by decide:2≠0)] at hq
    exact hp _ (sub_eq_zero.mp hq.symm)
  have hu:IsUnit (rootAt b p (chartIndex b p)):=
    IsLocalization.map_units (Stalk b p) ⟨_,hn⟩
  have hv:=ActualPrimeMeromorphicOrder318.value_source_unit (A b) (finitePrime b p) _ hu
  exact (congrArg (fun q:WithTop ℤ=>0+q) hv).trans (zero_add 0)
lemma branch_order(p:FinitePoints b)(i:Fin 4)(hp:p.val.1=b i):order b hb p=1:=by
  rw [order,branch_value b hb p i hp];rfl
lemma regular_order(p:FinitePoints b)(hp:∀i,p.val.1≠b i):order b hb p=0:=by
  rw [order,regular_value b hb p hp];rfl
lemma coefficient_ne_zero(p:FinitePoints b):coefficient b hb p≠0:=by
  intro he
  have ht:value b hb p=⊤:=by rw [value,he,AddValuation.map_zero]
  by_cases hp:∃i,p.val.1=b i
  · obtain ⟨i,hi⟩:=hp
    rw [branch_value b hb p i hi] at ht
    exact WithTop.coe_ne_top ht
  · rw [regular_value b hb p (by simpa only [not_exists] using hp)] at ht
    exact WithTop.coe_ne_top ht
end FourRootActualFiniteDifferentialOrders318

namespace FourRootActualInfinityDifferentialOrders318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualInfinityTraceTransport318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance infinityDedekind:IsDedekindDomain (FourRootInfinityCoordinateRing318.Ring b):=
  FourRootActualDedekind318.infinity_dedekind b hb
local instance pointPrime(p:InfinityPoints b):(infinityPrime b p).IsPrime:=infinity_prime b p
@[expose] def coefficient:FourRootActualMeromorphicInfinity318.F b:=
  FourRootActualMeromorphicInfinity318.frame b hb
    (KaehlerDifferential.D ℂ (FourRootActualMeromorphicInfinity318.F b)
      (FourRootActualMeromorphicInfinity318.t b hb))
@[expose] def value(p:InfinityPoints b)(hp:p.val.1=0):WithTop ℤ:=
  letI:=FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  ActualPrimeMeromorphicOrder318.value (FourRootInfinityCoordinateRing318.Ring b)
    (infinityPrime b p) (coefficient b hb)
@[expose] def order(p:InfinityPoints b)(hp:p.val.1=0):ℤ:=WithTop.untopD 0 (value b hb p hp)
/-- Genuine order MINUS THREE of the original dt at every one of the
eight actual infinity centers. The reciprocal dv has a different order. -/
theorem value_minus_three(p:InfinityPoints b)(hp:p.val.1=0):value b hb p hp=(-3:ℤ):=by
  letI:=FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  let I:=FourRootInfinityCoordinateRing318.Ring b
  let v:=ActualPrimeMeromorphicOrder318.value I (infinityPrime b p)
  have hu:v (FourRootActualMeromorphicInfinity318.u b)=1:=
    ActualPrimeMeromorphicOrder318.value_source_uniformizer I (infinityPrime b p)
      (FourRootInfinityCoordinateRing318.coordinate b none) (actual_infinity_uniformizer b hb p hp)
  have h2:v (2:FractionRing I)=0:=ActualPrimeMeromorphicOrder318.value_two I (infinityPrime b p)
  change v (coefficient b hb)=(-3:ℤ)
  rw [coefficient,FourRootActualMeromorphicInfinity318.dt_coefficient,
    v.map_mul,v.map_neg,v.map_pow,v.map_inv,hu,h2]
  norm_num
lemma order_minus_three(p:InfinityPoints b)(hp:p.val.1=0):order b hb p hp=-3:=by
  rw [order,value_minus_three];rfl
lemma coefficient_ne_zero:coefficient b hb≠0:=by
  rw [coefficient,FourRootActualMeromorphicInfinity318.dt_coefficient]
  exact mul_ne_zero (neg_ne_zero.mpr (by norm_num))
    (pow_ne_zero _ (inv_ne_zero (FourRootActualMeromorphicInfinity318.u_ne b hb)))
end FourRootActualInfinityDifferentialOrders318
