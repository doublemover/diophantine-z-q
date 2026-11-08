module
public import BothInfinityOrigin318
public import ChartNegation318
public section
noncomputable section
namespace InfinityBoundaryDoubling318
open BothInfinityAlgebra318 InfinityVietaAlgebra318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (A B:R) (f:InfinityChart318.Ring A B →ₐ[R] S)
variable (hz:f (InfinityChart318.z A B)=0)

include hz in
lemma cube_zero : f (InfinityChart318.x A B)^3=0 := by
  have h:=congrArg f (InfinityChart318.relation A B)
  simp only [map_sub,map_pow,map_mul,map_zero,hz,zero_pow (by decide:2≠0),
    zero_pow (by decide:3≠0),mul_zero,sub_zero,zero_sub,neg_eq_zero] at h
  exact h

@[expose] def pairMap : PairRing A B →ₐ[R] S :=
  Algebra.TensorProduct.lift f f (fun _ _=>Commute.all _ _)
lemma pair_left (a:InfinityChart318.Ring A B) : pairMap A B f (leftPair A B a)=f a := by
  simp [pairMap,leftPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
lemma pair_right (a:InfinityChart318.Ring A B) : pairMap A B f (rightPair A B a)=f a := by
  simp [pairMap,rightPair,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]
lemma pair_pow (a:PairRing A B) (n:ℕ) : pairMap A B f (a^n)=(pairMap A B f a)^n :=
  (pairMap A B f).toRingHom.map_pow a n
lemma pair_one : pairMap A B f 1=1 := (pairMap A B f).toRingHom.map_one
include hz in
lemma map_Q : pairMap A B f (Q A B)=1 := by
  simp only [Q,q,map_sub,map_mul,map_add,pair_pow,pair_one,U2,V1,V2,pair_left,pair_right,hz,
    zero_add,mul_zero,zero_mul,zero_pow (by decide:2≠0),add_zero,sub_zero]
include hz in
lemma map_S : pairMap A B f (BothInfinityAlgebra318.S A B)=3*f (InfinityChart318.x A B)^2 := by
  simp only [BothInfinityAlgebra318.S,s,map_add,map_mul,pair_pow,U1,U2,V1,pair_left,pair_right,hz,
    zero_pow (by decide:2≠0),mul_zero,add_zero]
  ring
include hz in
lemma slope_square : (3*f (InfinityChart318.x A B)^2)^2=0 := by
  linear_combination 9*f (InfinityChart318.x A B)*(cube_zero A B f hz)
include hz in
lemma slope_cube : (3*f (InfinityChart318.x A B)^2)^3=0 := by
  rw [pow_succ,slope_square A B f hz,zero_mul]
include hz in
lemma map_domain : pairMap A B f (domainElement A B)=1 := by
  simp only [domainElement,C,map_mul,map_add,pair_pow,map_Q A B f hz,map_S A B f hz,one_pow,mul_one,
    slope_square A B f hz,slope_cube A B f hz,mul_zero,add_zero]

@[expose] def lift : OutputRing A B →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=pairMap A B f) (domainElement A B)
    (by rw [map_domain A B f hz];exact isUnit_one)
lemma lift_pair (a:PairRing A B) : lift A B f hz (BothInfinityAlgebra318.pairMap A B a)=pairMap A B f a := by
  simp only [lift,BothInfinityAlgebra318.pairMap,IsLocalization.Away.liftAlgHom_apply,
    IsScalarTower.toAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl
lemma lift_pow (a:OutputRing A B) (n:ℕ) : lift A B f hz (a^n)=(lift A B f hz a)^n :=
  (lift A B f hz).toRingHom.map_pow a n
lemma map_slope : lift A B f hz (slope A B)=3*f (InfinityChart318.x A B)^2 := by
  have h:=congrArg (lift A B f hz) (slope_Q A B)
  simpa only [map_mul,lift_pair,map_Q A B f hz,map_S A B f hz,mul_one] using h
lemma map_intercept : lift A B f hz (intercept A B)=0 := by
  simp only [intercept,map_sub,map_mul,v1,u1,lift_pair,V1,U1,pair_left,hz,map_slope,zero_sub]
  linear_combination -3*(cube_zero A B f hz)
lemma map_outU : lift A B f hz (outU A B)=2*f (InfinityChart318.x A B) := by
  simp only [outU,d,map_add,map_mul,lift_pow,map_ofNat,u1,u2,lift_pair,U1,U2,pair_left,pair_right,
    map_intercept,mul_zero,add_zero,zero_mul]
  ring
lemma map_outV : lift A B f hz (outV A B)=0 := by
  simp only [outV,map_sub,map_mul,map_slope,map_outU,map_intercept,sub_zero]
  linear_combination 6*(cube_zero A B f hz)

lemma double_output : (lift A B f hz).comp (outputMap A B)=
    InfinityChart318.lift A B (2*f (InfinityChart318.x A B)) 0 (by
      simp only [zero_pow (by decide:2≠0),zero_pow (by decide:3≠0),mul_zero,sub_zero,zero_sub]
      rw [mul_pow,cube_zero A B f hz,mul_zero,neg_zero]) := by
  apply InfinityChart318.hom_ext
  · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_x] using map_outU A B f hz
  · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_z] using map_outV A B f hz

/-- On the actual nonreduced z=0 boundary, doubling equals negation only at
infinity when 3 is invertible. No reducedness or domain hypothesis is used. -/
theorem double_neg_iff (h3:IsUnit (3:S)) :
    (lift A B f hz).comp (outputMap A B)=f.comp (ChartNegation318.infinityNeg A B) ↔
      f=(Algebra.ofId R S).comp (InfinityChart318.origin A B) := by
  constructor
  · intro h
    have hx:=congrArg (fun g:InfinityChart318.Ring A B →ₐ[R] S=>g (InfinityChart318.x A B)) h
    simp only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_x,map_outU,
      ChartNegation318.infinityNeg_x,map_neg] at hx
    have hx0:f (InfinityChart318.x A B)=0 := by
      apply h3.mul_left_cancel
      linear_combination hx
    apply InfinityChart318.hom_ext
    · simpa only [AlgHom.comp_apply,InfinityChart318.origin_x,map_zero] using hx0
    · simpa only [AlgHom.comp_apply,InfinityChart318.origin_z,map_zero] using hz
  · intro h
    apply InfinityChart318.hom_ext
    · simp only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_x,map_outU,
        ChartNegation318.infinityNeg_x,map_neg]
      have hx:f (InfinityChart318.x A B)=0 := by rw [h];simp
      rw [hx,mul_zero,neg_zero]
    · simp only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_z,map_outV,
        ChartNegation318.infinityNeg_z,map_neg,hz,neg_zero]
end InfinityBoundaryDoubling318
