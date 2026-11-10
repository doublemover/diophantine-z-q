module
public import FourRootActualDedekind318
public import FourRootOffBranchRamification318
public import FourRootActualInfinityRamification318
public import Mathlib.RingTheory.DedekindDomain.Different
public section
noncomputable section
namespace FourRootActualTraceDifferentSupport318
open scoped Classical
open FourRootActualGenericField318 FourRootAffineTensorPresentation318 FourRootActualFractionField318
open FourRootActualResidueInertia318 FourRootNormalizedPointCharts318 FourRootOffBranchRamification318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDomain:IsDomain (A b):=affine_domain b hb
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance affineFinite:Module.Finite P (A b):=(FourRootActualOrderGalois318.finite_free b).1
local instance affineFree:Module.Free P (A b):=(FourRootActualOrderGalois318.finite_free b).2
local instance fractionSeparable:Algebra.IsSeparable (FractionRing P) (FractionRing (A b)):=inferInstance

/-- Actual trace-dual different of the whole original polynomial order,
not a renamed relative cotangent annihilator. -/
@[expose] def traceDifferent:Ideal (A b):=differentIdeal P (A b)
include hb in
lemma point_separable_under(p:FinitePoints b):
    Algebra.HasSeparableResidueFieldsAt P (A b) ((finitePrime b p).under P):=by
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  letI:(pointBase p.val.1).IsPrime:=(pointBase_maximal p.val.1).isPrime
  letI:(finitePrime b p).LiesOver (pointBase p.val.1):=point_liesOver b p
  have he:pointBase p.val.1=(finitePrime b p).under P:=Ideal.LiesOver.over
  rw [←he]
  exact point_separable b p.val.1
/-- Whole finite support of the TRACE-defined different is exactly the
four actual marked branch fibers. This uses the actual Dedekind order,
separable residues and established local algebraic indices. Multiplicity
one and equality with the Kähler annihilator are not assumed here. -/
theorem actual_trace_support(p:FinitePoints b):
    finitePrime b p∣traceDifferent b hb↔∃i:Fin 4,p.val.1=b i:=by
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  letI:Algebra.HasSeparableResidueFieldsAt P (A b) ((finitePrime b p).under P):=
    point_separable_under b hb p
  rw [traceDifferent,dvd_differentIdeal_iff,
    ←Ideal.ramificationIdx_eq_one_iff,finite_exact_index b hb p]
  by_cases h:∃i:Fin 4,p.val.1=b i <;> simp [h]
end FourRootActualTraceDifferentSupport318

namespace FourRootActualInfinityTraceDifferent318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev P:=Polynomial ℂ
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance infinityBase:Algebra P (I b):=
  (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2)).toAlgebra
local instance infinityDomain:IsDomain (I b):=FourRootInfinityDomain318.infinity_domain b hb
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
local instance infinityFinite:Module.Finite P (I b):=(FourRootSquaredInfinityBase318.finite_free b).1
local instance infinityFree:Module.Free P (I b):=(FourRootSquaredInfinityBase318.finite_free b).2
local instance fractionSeparable:Algebra.IsSeparable (FractionRing P) (FractionRing (I b)):=inferInstance
@[expose] def traceDifferent:Ideal (I b):=differentIdeal P (I b)
/-- Each of the eight actual infinity centers is genuinely in the support
of the TRACE-defined different over v, by its actual algebraic index2. -/
theorem actual_infinity_trace_support(p:InfinityPoints b) (hp:p.val.1=0):
    infinityPrime b p∣traceDifferent b hb:=by
  letI:(infinityPrime b p).IsPrime:=infinity_prime b p
  rw [traceDifferent,dvd_differentIdeal_iff]
  intro h
  letI:Algebra.IsUnramifiedAt P (infinityPrime b p):=h
  have he:=(infinityPrime b p).ramificationIdx_eq_one P
  rw [FourRootActualInfinityRamification318.ramificationIdx_two b hb p hp] at he
  norm_num at he
end FourRootActualInfinityTraceDifferent318
