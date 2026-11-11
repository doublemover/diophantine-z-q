module
public import FourRootInfinityAffineComparison318
public import PolynomialOrderIsomorphismInertia318
public import FourRootInfinityDomain318
public section
noncomputable section
namespace FourRootActualInfinityRamification318
open Polynomial FourRootReciprocalBranchData318 FourRootInfinityAffineComparison318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev P:=Polynomial ℂ
local instance infinityAlgebra:Algebra P (I b):=(Polynomial.aeval (iz b none^2)).toAlgebra
local instance finiteAlgebra:Algebra P (A b):=(Polynomial.aeval (az b none)).toAlgebra
local instance infinityDomain:IsDomain (I b):=FourRootInfinityDomain318.infinity_domain b hb
local instance infinityFinite:Module.Finite P (I b):=(FourRootSquaredInfinityBase318.finite_free b).1
local instance infinityFree:Module.Free P (I b):=(FourRootSquaredInfinityBase318.finite_free b).2
local instance infinityFlat:Module.Flat P (I b):=Module.Flat.of_free
abbrev G:=I b≃ₐ[P]I b

lemma group_finite:Finite (G b):=by
  letI:Finite (A b≃ₐ[P]A b):=
    FourRootActualOrderGalois318.group_finite (branches b) (branches_injective b hb)
  exact Finite.of_equiv (A b≃ₐ[P]A b)
    (PolynomialOrderIsomorphismInertia318.conjugation (polynomialEquivalence b hb)).symm
lemma invariant:Algebra.IsInvariant P (I b) (G b):=
  PolynomialOrderIsomorphismInertia318.invariant (polynomialEquivalence b hb)
    (FourRootActualOrderGalois318.invariant (branches b) (branches_injective b hb))
lemma galoisGroup:IsGaloisGroup (G b) P (I b) where
  faithful:=inferInstance
  commutes:=inferInstance
  isInvariant:=invariant b hb
local instance groupFinite:Finite (G b):=group_finite b hb
local instance groupGalois:IsGaloisGroup (G b) P (I b):=galoisGroup b hb

/-- Each of the eight actual infinity points is carried to an actual
finite branch-zero point, with its entire evaluation map retained. -/
@[expose] def finitePoint (p:InfinityPoints b):FinitePoints (branches b):=
  FourRootAffineCoordinateRing318.point (branches b)
    ((infinityEvaluation b p).comp (fromAffine b hb))
lemma finitePoint_base (p:InfinityPoints b):
    (finitePoint b hb p).val.1=p.val.1^2:=by
  change infinityEvaluation b p (fromAffine b hb (az b none))=_
  rw [fromAffine_base,map_pow]
  rfl
lemma transformed_kernel (p:InfinityPoints b):
    RingHom.ker ((infinityEvaluation b p).toRingHom.comp
      (polynomialEquivalence b hb).symm.toRingHom)=
        finitePrime (branches b) (finitePoint b hb p):=by
  have h:finiteEvaluation (branches b) (finitePoint b hb p)=
      (infinityEvaluation b p).comp (fromAffine b hb):=
    (FourRootAffineCoordinateRing318.pointEquiv (branches b)).symm_apply_apply _
  rw [finitePrime,h]
  rfl
lemma full_inertia_card (p:InfinityPoints b) (hp:p.val.1=0):
    Nat.card ((infinityPrime b p).inertia (G b))=2:=by
  have hc:=Nat.card_congr (PolynomialOrderIsomorphismInertia318.inertiaEquivalence
    (polynomialEquivalence b hb) (infinityEvaluation b p).toRingHom)
  rw [transformed_kernel] at hc
  have hq:(finitePoint b hb p).val.1=branches b 0:=by
    rw [finitePoint_base,hp,zero_pow (by decide:2≠0),branches_zero]
  exact hc.trans (FourRootFullFiniteInertia318.full_inertia_card (branches b)
    (branches_injective b hb) 0 (finitePoint b hb p) hq)

@[expose] def basePrime:Ideal P:=Ideal.span {X}
lemma base_maximal:(basePrime).IsMaximal:=by
  have h:=FourRootActualFiniteRamification318.contact_maximal (fun _:Fin 4=>(0:ℂ)) 0
  simpa only [FourRootActualFiniteRamification318.contactPrime,C_0,sub_zero] using h
lemma liesOver (p:InfinityPoints b) (hp:p.val.1=0):
    (infinityPrime b p).LiesOver basePrime:=by
  letI:(infinityPrime b p).IsPrime:=infinity_prime b p
  constructor
  apply base_maximal.eq_of_le
    (Ideal.IsPrime.ne_top (inferInstance:((infinityPrime b p).under P).IsPrime))
  apply Ideal.span_le.mpr
  intro r hr
  rcases Set.mem_singleton_iff.mp hr with rfl
  change infinityEvaluation b p (Polynomial.aeval (iz b none^2) X)=0
  rw [Polynomial.aeval_X,map_pow]
  change p.val.1^2=0
  rw [hp,zero_pow (by decide:2≠0)]
lemma separableResidue:Algebra.HasSeparableResidueFieldsAt P (I b) basePrime:=by
  letI:basePrime.IsPrime:=base_maximal.isPrime
  letI:Algebra.IsIntegral P (I b):=Algebra.IsIntegral.of_finite P (I b)
  letI:Algebra ℂ basePrime.ResidueField:=
    ((algebraMap P basePrime.ResidueField).comp (algebraMap ℂ P)).toAlgebra
  letI:CharZero basePrime.ResidueField:=Algebra.charZero_of_charZero ℂ basePrime.ResidueField
  infer_instance

/-- Algebraic ramification index two at EVERY one of the eight actual
normalized infinity points, over the actual reciprocal base v=u².
The rank-eight u-presentation is never substituted for that degree-sixteen base. -/
theorem ramificationIdxIn_two (p:InfinityPoints b) (hp:p.val.1=0):
    Ideal.ramificationIdxIn basePrime (I b)=2:=by
  letI:basePrime.IsPrime:=base_maximal.isPrime
  letI:(infinityPrime b p).IsPrime:=infinity_prime b p
  letI:(infinityPrime b p).LiesOver basePrime:=liesOver b p hp
  letI:Algebra.HasSeparableResidueFieldsAt P (I b) basePrime:=separableResidue b
  have h:=Ideal.card_inertia_eq_ramificationIdxIn (G:=G b) basePrime (infinityPrime b p)
  exact h.symm.trans (full_inertia_card b hb p hp)
theorem ramificationIdx_two (p:InfinityPoints b) (hp:p.val.1=0):
    (infinityPrime b p).ramificationIdx P=2:=by
  letI:basePrime.IsPrime:=base_maximal.isPrime
  letI:(infinityPrime b p).IsPrime:=infinity_prime b p
  letI:(infinityPrime b p).LiesOver basePrime:=liesOver b p hp
  rw [←Ideal.ramificationIdxIn_eq_ramificationIdx basePrime (infinityPrime b p) (G b)]
  exact ramificationIdxIn_two b hb p hp
end FourRootActualInfinityRamification318
