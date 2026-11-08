module
public import InfinityKernelNeighborhoodAlgebra318
public section
noncomputable section
namespace InfinityKernelNeighborhoodOrigin318
open BothInfinityAlgebra318 InfinityVietaAlgebra318 InfinityKernelNeighborhoodAlgebra318
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R T:Type*} [CommRing R] [CommRing T]

/-- The literal denominator is 3 at every origin-valued ring map. This is
also the exact prime-ideal test needed for the complementary kernel open. -/
theorem denominator_at_zero (A B:R) (f:InfinityChart318.Ring A B →+* T)
    (hx:f (InfinityChart318.x A B)=0) (hz:f (InfinityChart318.z A B)=0) :
    f (denominator A B)=3 := by
  let ψ:PairRing A B →+* T:=f.comp (diagonal A B).toRingHom
  have hleft (a:InfinityChart318.Ring A B):ψ (leftPair A B a)=f a := by
    change f (InfinityBoundaryDoubling318.pairMap A B (AlgHom.id R _) (leftPair A B a))=f a
    rw [InfinityBoundaryDoubling318.pair_left,AlgHom.id_apply]
  have hright (a:InfinityChart318.Ring A B):ψ (rightPair A B a)=f a := by
    change f (InfinityBoundaryDoubling318.pairMap A B (AlgHom.id R _) (rightPair A B a))=f a
    rw [InfinityBoundaryDoubling318.pair_right,AlgHom.id_apply]
  have hQ:ψ (BothInfinityAlgebra318.Q A B)=1 := by
    simp only [BothInfinityAlgebra318.Q,q,map_sub,map_one,map_add,map_mul,map_pow,U2,V1,V2,
      hleft,hright,hx,hz,zero_add,mul_zero,zero_mul,zero_pow (by decide:2≠0),sub_zero]
  have hS:ψ (BothInfinityAlgebra318.S A B)=0 := by
    simp only [BothInfinityAlgebra318.S,s,map_add,map_mul,map_pow,U1,U2,V1,hleft,hright,hx,hz,
      zero_add,mul_zero,zero_mul,zero_pow (by decide:2≠0)]
  have hd:ψ (domainElement A B)=1 := by
    simp only [domainElement,C,map_mul,map_add,map_pow,hQ,hS,one_pow,mul_one,
      zero_pow (by decide:2≠0),zero_pow (by decide:3≠0),mul_zero,add_zero]
  have hg:f (g A B)=1 := by
    simp only [g,InfinityKernelNeighborhoodPolynomial318.G,map_sub,map_one,map_mul,map_pow,hz,
      zero_pow (by decide:2≠0),mul_zero,sub_zero]
  have hh:f (h A B)=3 := by
    simp only [h,InfinityKernelNeighborhoodPolynomial318.H,InfinityKernelNeighborhoodPolynomial318.G,
      InfinityKernelNeighborhoodPolynomial318.C,InfinityKernelNeighborhoodPolynomial318.K,
      InfinityKernelNeighborhoodPolynomial318.Q,InfinityKernelNeighborhoodPolynomial318.S,q,s,
      map_sub,map_one,map_add,map_mul,map_pow,map_ofNat,hx,hz,
      zero_pow (by decide:2≠0),zero_pow (by decide:3≠0),zero_add,add_zero,mul_zero,zero_mul,
      sub_zero,one_pow,mul_one,one_mul]
  change f (diagonal A B (domainElement A B)*g A B*h A B)=3
  rw [map_mul,map_mul,hg,hh,mul_one]
  change ψ (domainElement A B)*3=3
  rw [hd,one_mul]

lemma origin_denominator (A B:R) : InfinityChart318.origin A B (denominator A B)=3 :=
  denominator_at_zero A B (InfinityChart318.origin A B).toRingHom
    (InfinityChart318.origin_x A B) (InfinityChart318.origin_z A B)

@[expose] def originLift (A B:R) (h3:IsUnit (3:R)) : Ring A B →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (f:=InfinityChart318.origin A B) (denominator A B)
    (by rw [origin_denominator];exact h3)
lemma originLift_input (A B:R) (h3:IsUnit (3:R)) (a:InfinityChart318.Ring A B) :
    originLift A B h3 (input A B a)=InfinityChart318.origin A B a := by
  simp only [originLift,input,IsLocalization.Away.liftAlgHom_apply,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl
end InfinityKernelNeighborhoodOrigin318
