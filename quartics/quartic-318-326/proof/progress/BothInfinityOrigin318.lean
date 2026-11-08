module
public import BothInfinityScheme318
import all WeierstrassGluing318
public section
noncomputable section
namespace BothInfinityOrigin318
open BothInfinityAlgebra318 InfinityVietaAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def pairOrigin (A B:R) : PairRing A B →ₐ[R] R :=
  Algebra.TensorProduct.lift (InfinityChart318.origin A B) (InfinityChart318.origin A B)
    (fun _ _=>Commute.all _ _)
lemma pairOrigin_left (A B:R) (r:InfinityChart318.Ring A B) :
    pairOrigin A B (leftPair A B r)=InfinityChart318.origin A B r := by
  simp [pairOrigin,leftPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
lemma pairOrigin_right (A B:R) (r:InfinityChart318.Ring A B) :
    pairOrigin A B (rightPair A B r)=InfinityChart318.origin A B r := by
  simp [pairOrigin,rightPair,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]
lemma pairOrigin_pow (A B:R) (r:PairRing A B) (n:ℕ) : pairOrigin A B (r^n)=(pairOrigin A B r)^n :=
  (pairOrigin A B).toRingHom.map_pow r n
lemma origin_coords (A B:R) : pairOrigin A B (U1 A B)=0 ∧ pairOrigin A B (V1 A B)=0 ∧
    pairOrigin A B (U2 A B)=0 ∧ pairOrigin A B (V2 A B)=0 := by
  simp [U1,V1,U2,V2,pairOrigin_left,pairOrigin_right]
lemma origin_Q (A B:R) : pairOrigin A B (Q A B)=1 := by
  simp only [Q,q,map_sub,map_mul,map_add,pairOrigin_pow,origin_coords A B |>.1,
    origin_coords A B |>.2.1,origin_coords A B |>.2.2.1,origin_coords A B |>.2.2.2,
    map_one,zero_add,mul_zero,zero_mul,zero_pow (by decide : 2≠0),sub_zero]
  exact (pairOrigin A B).toRingHom.map_one
lemma origin_S (A B:R) : pairOrigin A B (S A B)=0 := by
  simp only [S,s,map_mul,map_add,pairOrigin_pow,origin_coords A B |>.1,
    origin_coords A B |>.2.1,origin_coords A B |>.2.2.1,
    zero_add,mul_zero,zero_mul,zero_pow (by decide : 2≠0)]
lemma origin_domainElement (A B:R) : pairOrigin A B (domainElement A B)=1 := by
  simp only [domainElement,C,map_mul,map_add,pairOrigin_pow,origin_Q,origin_S,
    one_pow,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),mul_zero,zero_mul,
    add_zero,mul_one]

/-- The original-base pair of infinity sections lifts into the actual principal domain. -/
@[expose] def originLift (A B:R) : OutputRing A B →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (f:=pairOrigin A B) (domainElement A B)
    (by rw [origin_domainElement A B]; exact isUnit_one)
lemma originLift_pair (A B:R) (r:PairRing A B) :
    originLift A B (pairMap A B r)=pairOrigin A B r := by
  simp only [originLift,pairMap,IsLocalization.Away.liftAlgHom_apply,
    IsScalarTower.toAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl
lemma originLift_pow (A B:R) (r:OutputRing A B) (n:ℕ) : originLift A B (r^n)=(originLift A B r)^n :=
  (originLift A B).toRingHom.map_pow r n
lemma origin_slope (A B:R) : originLift A B (slope A B)=0 := by
  simp only [slope,map_mul,originLift_pair,origin_S,zero_mul]
lemma origin_intercept (A B:R) : originLift A B (intercept A B)=0 := by
  simp only [intercept,v1,map_sub,map_mul,originLift_pair,origin_coords A B |>.2.1,origin_slope,zero_mul,sub_zero]
lemma origin_output (A B:R) : originLift A B (outU A B)=0 ∧ originLift A B (outV A B)=0 := by
  have hu : originLift A B (outU A B)=0 := by
    simp only [outU,d,u1,u2,map_add,map_mul,originLift_pow,originLift_pair,origin_slope,origin_intercept,
      origin_coords A B |>.1,origin_coords A B |>.2.2.1,zero_pow (by decide : 2≠0),mul_zero,zero_mul,add_zero]
  refine ⟨hu,?_⟩
  simp only [outV,map_sub,map_mul,hu,origin_slope,origin_intercept,mul_zero,sub_zero]
lemma origin_outputMap (A B:R) : (originLift A B).comp (outputMap A B)=InfinityChart318.origin A B := by
  apply InfinityChart318.hom_ext
  · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_x,InfinityChart318.origin_x] using (origin_output A B).1
  · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_z,InfinityChart318.origin_z] using (origin_output A B).2

lemma origin_leftInput (A B:R) : (originLift A B).comp (BothInfinityScheme318.leftInput A B)=InfinityChart318.origin A B := by
  apply AlgHom.ext
  intro a
  change originLift A B (pairMap A B (leftPair A B a))=InfinityChart318.origin A B a
  rw [originLift_pair,pairOrigin_left]
lemma origin_rightInput (A B:R) : (originLift A B).comp (BothInfinityScheme318.rightInput A B)=InfinityChart318.origin A B := by
  apply AlgHom.ext
  intro a
  change originLift A B (pairMap A B (rightPair A B a))=InfinityChart318.origin A B a
  rw [originLift_pair,pairOrigin_right]

@[expose] def originSection (A B:R) : Spec (CommRingCat.of R) ⟶ BothInfinityScheme318.domain A B :=
  Spec.map (CommRingCat.ofHom (originLift A B).toRingHom)

theorem section_output (A B:R) : originSection A B ≫ BothInfinityScheme318.addition A B=
    WeierstrassGluing318.infinity A B := by
  change Spec.map (CommRingCat.ofHom (originLift A B).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (outputMap A B).toRingHom) ≫ WeierstrassGluing318.infinityChart A B)=_
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((originLift A B).comp (outputMap A B)).toRingHom) ≫ _=_
  rw [origin_outputMap]
  rfl

theorem section_left (A B:R) : originSection A B ≫ BothInfinityScheme318.intoProduct A B ≫ pullback.fst _ _=
    InfinitySmooth318.infinity A B := by
  rw [BothInfinityScheme318.intoProduct_fst]
  change Spec.map (CommRingCat.ofHom (originLift A B).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (BothInfinityScheme318.leftInput A B).toRingHom)=_
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((originLift A B).comp (BothInfinityScheme318.leftInput A B)).toRingHom)=_
  rw [origin_leftInput]
  rfl

theorem section_right (A B:R) : originSection A B ≫ BothInfinityScheme318.intoProduct A B ≫ pullback.snd _ _=
    InfinitySmooth318.infinity A B := by
  rw [BothInfinityScheme318.intoProduct_snd]
  change Spec.map (CommRingCat.ofHom (originLift A B).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (BothInfinityScheme318.rightInput A B).toRingHom)=_
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((originLift A B).comp (BothInfinityScheme318.rightInput A B)).toRingHom)=_
  rw [origin_rightInput]
  rfl

end BothInfinityOrigin318
