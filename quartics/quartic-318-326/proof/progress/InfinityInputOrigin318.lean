module
public import InfinityInputAlgebra318
public section
noncomputable section
namespace InfinityInputOrigin318
open InfinityInputAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

/-- The actual tensor-algebra specialization with its first input equal to infinity. -/
@[expose] def originPair (A B:R) : PairRing A B →ₐ[R] ShortAffineJacobian318.Ring A B :=
  Algebra.TensorProduct.lift ((Algebra.ofId R (ShortAffineJacobian318.Ring A B)).comp (InfinityChart318.origin A B))
    (AlgHom.id R (ShortAffineJacobian318.Ring A B)) (fun _ _ => Commute.all _ _)

@[simp] theorem originPair_left (A B:R) (a:InfinityChart318.Ring A B) :
    originPair A B (left A B a)=algebraMap R (ShortAffineJacobian318.Ring A B) (InfinityChart318.origin A B a) := by
  simp [originPair,left,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
@[simp] theorem originPair_right (A B:R) (a:ShortAffineJacobian318.Ring A B) :
    originPair A B (right A B a)=a := by
  simp [originPair,right,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]

theorem origin_values (A B:R) : originPair A B (u A B)=0 ∧ originPair A B (v A B)=0 ∧
    originPair A B (parameter A B)=1 ∧ originPair A B (denominator A B)=1 ∧
    originPair A B (numeratorX A B)=ShortAffineJacobian318.x A B ∧
    originPair A B (numeratorY A B)=ShortAffineJacobian318.y A B := by
  have hm (a:PairRing A B) (n:ℕ) : originPair A B (a^n)=(originPair A B a)^n := by
    induction n with
    | zero =>
        simp only [pow_zero]
        exact (originPair A B).toRingHom.map_one
    | succ n ih => simp only [pow_succ,map_mul,ih]
  have h1 : originPair A B 1=1 := (originPair A B).toRingHom.map_one
  simp only [u,v,x,y,parameter,denominator,numeratorX,numeratorY,
    InfinityInputPolynomial318.denominator,InfinityInputPolynomial318.numeratorX,
    InfinityInputPolynomial318.numeratorY,map_sub,map_mul,hm,map_add,h1,map_ofNat,
    originPair_left,originPair_right,InfinityChart318.origin_x,InfinityChart318.origin_z,
    map_zero,coeff,Algebra.ofId_apply,AlgHom.commutes]
  ring_nf
  simp

@[expose] def originLift (A B:R) : OutputRing A B →ₐ[R] ShortAffineJacobian318.Ring A B :=
  IsLocalization.Away.liftAlgHom (f:=originPair A B) (denominator A B)
    (by rw [(origin_values A B).2.2.2.1]; exact isUnit_one)
@[simp] theorem originLift_pair (A B:R) (a:PairRing A B) :
    originLift A B (pairMap A B a)=originPair A B a := by
  simp [originLift,pairMap,IsLocalization.Away.liftAlgHom_apply]

theorem originLift_inverse (A B:R) : originLift A B (↑(denominatorUnit A B)⁻¹)=1 := by
  have hk : pairMap A B (denominator A B)*↑(denominatorUnit A B)⁻¹=1 := by
    rw [←(denominator_unit A B).unit_spec]
    exact Units.mul_inv _
  have hh:=congrArg (originLift A B) hk
  simpa only [map_mul,map_one,originLift_pair,(origin_values A B).2.2.2.1,one_mul] using hh

/-- The actual output algebra map specializes to the identity on the entire finite chart. -/
theorem origin_output_identity (A B:R) :
    (originLift A B).comp (outputMap A B)=AlgHom.id R (ShortAffineJacobian318.Ring A B) := by
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,outputMap_x,outX,map_mul,map_pow,originLift_pair,
      (origin_values A B).2.2.2.2.1,originLift_inverse,one_pow,mul_one,AlgHom.id_apply]
  · simp only [AlgHom.comp_apply,outputMap_y,outY,map_mul,map_pow,originLift_pair,
      (origin_values A B).2.2.2.2.2,originLift_inverse,one_pow,mul_one,AlgHom.id_apply]

end InfinityInputOrigin318
