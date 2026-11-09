module
public import ThreeJArithmeticAlgebraMap318
public import ThreeNormalizedInverse318
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
namespace ThreeRationalFixed318
open Polynomial ThreeJArithmeticAlgebraMap318
open scoped TensorProduct
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Rational base change of the original integral diamond-fixed algebra.
It is not silently identified with the unchanged integral target. -/
abbrev Ring := ℚ ⊗[ℤ] Fixed
@[expose] def includeFixed : Fixed →ₐ[ℤ] Ring := Algebra.TensorProduct.includeRight
@[expose] def baseMap : OpenJModel318.Base 3 →+* Ring :=
  includeFixed.toRingHom.comp (algebraMap (OpenJModel318.Base 3) Fixed)
@[expose] def j : Ring := baseMap (OpenJModel318.jCoord 3)
@[expose] def v : Ring := baseMap (OpenJModel318.inverseDenominator 3)
@[expose] def k : Ring := j*v
@[expose] def x : Ring := includeFixed (ModularArithmeticCoordinates318.xGenerator 3)
lemma jv : (j-1728)*v=1 := by
  simpa only [j,v,map_mul,map_sub,map_ofNat,map_one] using
    congrArg baseMap (OpenJModel318.denominator_inverse 3)
lemma j_units : IsUnit j ∧ IsUnit (j-1728) := by
  constructor
  · exact ((OpenJModel318.base_units 3).2.2.2.1).map baseMap
  · simpa only [map_sub,map_ofNat] using
      ((OpenJModel318.base_units 3).2.2.2.2).map baseMap
lemma k_unit : IsUnit k := j_units.1.mul (IsUnit.of_mul_eq_one_right _ jv)
lemma k_sub : k-1=1728*v := by
  unfold k
  linear_combination jv
lemma k_sub_unit : IsUnit (k-1) := by
  rw [k_sub]
  exact (ThreeNormalizedInverse318.positive_nat_unit 1728 (by decide)).mul
    (IsUnit.of_mul_eq_one_right _ jv)
lemma k_j_sub : k*(j-1728)=j := by
  unfold k
  linear_combination j*jv

lemma base_A : baseMap (OpenJAffineScheme318.A 3)= -3*k := by
  simp only [OpenJAffineScheme318.A,map_mul,map_neg,map_ofNat,j,v,k]
  ring
lemma base_B : baseMap (OpenJAffineScheme318.B 3)= -2*k := by
  simp only [OpenJAffineScheme318.B,map_mul,map_neg,map_ofNat,j,v,k]
  ring

lemma root_relation : ThreeNormalizedInverse318.relation k x=0 := by
  let f : XRing →+* Ring := includeFixed.toRingHom.comp fixedEquiv.toRingEquiv.toRingHom
  have h := congrArg f (ShortThreeTorsion318.division_zero A B)
  have hf (r : OpenJModel318.Base 3) : f (AdjoinRoot.of
      (ShortThreeTorsion318.polynomial A B) r)=baseMap r := by
    change includeFixed (fixedEquiv (algebraMap (OpenJModel318.Base 3) XRing r))=_
    rw [AlgEquiv.commutes]
    rfl
  have hx : f (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B))=x := rfl
  simp only [ThreeTorsionIdentity318.divisionPolynomial,map_sub,map_add,map_mul,map_pow,
    map_ofNat,AdjoinRoot.mk_X,AdjoinRoot.mk_C,hf,hx,base_A,base_B,map_zero] at h
  have h3 : IsUnit (3:Ring) := ThreeNormalizedInverse318.positive_nat_unit 3 (by decide)
  apply h3.mul_right_eq_zero.mp
  unfold ThreeNormalizedInverse318.relation
  linear_combination h

@[expose] def parameter : Ring :=
  ThreeNormalizedInverse318.parameter k x k_unit k_sub_unit root_relation
lemma parameter_unit : IsUnit parameter :=
  ThreeNormalizedInverse318.parameter_unit k x k_unit k_sub_unit root_relation
lemma parameter_D_unit : IsUnit (parameter^2-486*parameter-19683) :=
  ThreeNormalizedInverse318.D_unit k x k_unit k_sub_unit root_relation
lemma parameter_x : x*(parameter^2-486*parameter-19683)=
    3*(parameter+27)*(parameter+243) :=
  ThreeNormalizedInverse318.X_parameter k x k_unit k_sub_unit root_relation
lemma parameter_j : (parameter+27)*(parameter+243)^3=j*parameter^3 := by
  have h := ThreeNormalizedInverse318.J_parameter k x k_unit k_sub_unit root_relation
  have hk : j*(k-1)=1728*k := by
    linear_combination k_j_sub
  apply k_sub_unit.mul_left_cancel
  change (k-1)*((parameter+27)*(parameter+243)^3)=(k-1)*(j*parameter^3)
  linear_combination h-hk*parameter^3

end ThreeRationalFixed318
