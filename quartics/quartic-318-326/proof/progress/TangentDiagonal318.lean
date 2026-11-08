module
public import TangentOpenScheme318
public import ChartNegation318
public section
noncomputable section
namespace TangentDiagonal318
open Polynomial TangentOpenAlgebra318
open RelativeChordAlgebra318 (PairRing leftPair rightPair)
open scoped TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S] (A B:R)
  (φ:ShortAffineJacobian318.Ring A B→ₐ[R]S)

@[expose] def pair : PairRing A B→ₐ[R]S :=
  Algebra.TensorProduct.lift φ φ (fun _ _=>Commute.all _ _)
@[simp] theorem pair_left (z:ShortAffineJacobian318.Ring A B) :
    pair A B φ (leftPair A B z)=φ z:=by
  simp only [pair,leftPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul,map_one,mul_one]
@[simp] theorem pair_right (z:ShortAffineJacobian318.Ring A B) :
    pair A B φ (rightPair A B z)=φ z:=by
  simp only [pair,rightPair,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul,map_one,one_mul]

variable (hu:IsUnit (2*φ (ShortAffineJacobian318.y A B)))
@[expose] def diagonal : TangentRing A B→ₐ[R]S :=
  IsLocalization.Away.liftAlgHom (f:=pair A B φ) (ordinateSum A B) (by
    simpa only [ordinateSum,map_add,pair_left,pair_right,two_mul] using hu)

@[simp] theorem diagonal_left (z:ShortAffineJacobian318.Ring A B) :
    diagonal A B φ hu (left A B z)=φ z:=by
  simp only [left,AlgHom.comp_apply,IsScalarTower.toAlgHom_apply,diagonal,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,pair_left]
@[simp] theorem diagonal_right (z:ShortAffineJacobian318.Ring A B) :
    diagonal A B φ hu (right A B z)=φ z:=by
  simp only [right,AlgHom.comp_apply,IsScalarTower.toAlgHom_apply,diagonal,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,pair_right]

lemma slope_relation : diagonal A B φ hu (slope A B)*(2*φ (ShortAffineJacobian318.y A B))=
    3*(φ (ShortAffineJacobian318.x A B))^2+algebraMap R S A:=by
  have hh:=congrArg (diagonal A B φ hu) (slope_sum A B)
  simp only [map_mul,map_add,map_pow,AlgHom.commutes,x1,y1,x2,y2,
    diagonal_left,diagonal_right] at hh
  linear_combination hh

lemma curve_relation : (φ (ShortAffineJacobian318.y A B))^2=
    (φ (ShortAffineJacobian318.x A B))^3+algebraMap R S A*φ (ShortAffineJacobian318.x A B)+
      algebraMap R S B:=by
  have hh:=congrArg φ (ShortAffineJacobian318.relation A B)
  simp only [map_sub,map_pow,map_mul,AlgHom.commutes,map_zero] at hh
  linear_combination hh

end TangentDiagonal318
