module
public import ThreeRationalFixed318
public section
noncomputable section
namespace ThreeRationalModuliInverse318
open Polynomial
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def backwardLaurent : ThreeJLaurentEquiv318.Laurent →ₐ[ℚ] ThreeRationalFixed318.Ring :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) ThreeRationalFixed318.parameter)
    (Polynomial.X:ℚ[X]) (by simpa only [Polynomial.aeval_X] using
      ThreeRationalFixed318.parameter_unit)
lemma backwardLaurent_t : backwardLaurent ProjectiveLineOverlap318.t=ThreeRationalFixed318.parameter := by
  simp only [backwardLaurent,ProjectiveLineOverlap318.t,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,Polynomial.aeval_X]
lemma backwardLaurent_ts :
    ThreeRationalFixed318.parameter * backwardLaurent ProjectiveLineOverlap318.s=1 := by
  simpa only [map_mul,map_one,backwardLaurent_t] using
    congrArg backwardLaurent ProjectiveLineOverlap318.ts
lemma backwardLaurent_j : backwardLaurent ThreeJLaurentEquiv318.jLaurent=ThreeRationalFixed318.j := by
  simp only [ThreeJLaurentEquiv318.jLaurent,map_mul,map_pow,map_add,map_ofNat,backwardLaurent_t]
  rw [ThreeRationalFixed318.parameter_j,mul_assoc,←mul_pow,backwardLaurent_ts,one_pow,mul_one]
lemma backward_deleted_unit : IsUnit (backwardLaurent ThreeJModuliOpen318.deleted) := by
  rw [ThreeJModuliOpen318.deleted,map_mul,map_sub,map_ofNat,backwardLaurent_j]
  exact ThreeRationalFixed318.j_units.1.mul ThreeRationalFixed318.j_units.2

/-- Constructed inverse on the rational base change of the literal fixed
algebra, using its own quartic relation and unit certificates. -/
@[expose] def backward : ThreeJModuliOpen318.Ring →ₐ[ℚ] ThreeRationalFixed318.Ring :=
  IsLocalization.Away.liftAlgHom (f:=backwardLaurent) ThreeJModuliOpen318.deleted
    backward_deleted_unit
lemma backward_inclusion (a : ThreeJLaurentEquiv318.Laurent) :
    backward (ThreeJModuliOpen318.inclusion a)=backwardLaurent a := by
  simp only [backward,ThreeJModuliOpen318.inclusion,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
lemma backward_t : backward ThreeJModuliOpen318.t=ThreeRationalFixed318.parameter := by
  rw [ThreeJModuliOpen318.t,backward_inclusion,backwardLaurent_t]
lemma backward_j : backward ThreeJModuliOpen318.j=ThreeRationalFixed318.j := by
  rw [ThreeJModuliOpen318.j,backward_inclusion,backwardLaurent_j]
lemma backward_d : backward ThreeJModuliOpen318.d=
    ThreeRationalFixed318.parameter^2-486*ThreeRationalFixed318.parameter-19683 := by
  simp only [ThreeJModuliOpen318.d,map_sub,map_pow,map_mul,map_ofNat,backward_t]
lemma backward_x : backward ThreeJModuliOpen318.x=ThreeRationalFixed318.x := by
  have h := congrArg backward ThreeJModuliOpen318.dv
  simp only [map_mul,map_one,backward_d] at h
  apply ThreeRationalFixed318.parameter_D_unit.mul_left_cancel
  simp only [ThreeJModuliOpen318.x,map_mul,map_add,map_ofNat,backward_t]
  linear_combination 3*(ThreeRationalFixed318.parameter+27)*
    (ThreeRationalFixed318.parameter+243)*h-ThreeRationalFixed318.parameter_x

@[expose] def forward : ThreeRationalFixed318.Ring →ₐ[ℚ] ThreeJModuliOpen318.Ring :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ _) ThreeJArithmeticAlgebraMap318.fixedMap.toIntAlgHom
    (fun _ _ => Commute.all _ _)
lemma forward_fixed (a : ThreeJArithmeticAlgebraMap318.Fixed) :
    forward (ThreeRationalFixed318.includeFixed a)=ThreeJArithmeticAlgebraMap318.fixedMap a := by
  simp only [forward,ThreeRationalFixed318.includeFixed,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul,Algebra.ofId_apply,map_one,one_mul,RingHom.toIntAlgHom_apply]
lemma forward_j : forward ThreeRationalFixed318.j=ThreeJModuliOpen318.j := by
  change forward (ThreeRationalFixed318.includeFixed _)=_
  rw [forward_fixed,ThreeJArithmeticAlgebraMap318.fixedMap_j]
lemma forward_x : forward ThreeRationalFixed318.x=ThreeJModuliOpen318.x := by
  rw [ThreeRationalFixed318.x,forward_fixed,ThreeJArithmeticAlgebraMap318.fixedMap_x]
lemma forward_v : forward ThreeRationalFixed318.v=
    ThreeJModuliOpen318.baseMap (OpenJModel318.inverseDenominator 3) := by
  change forward (ThreeRationalFixed318.includeFixed _)=_
  rw [forward_fixed,ThreeJArithmeticAlgebraMap318.fixedMap_base]
lemma forward_k : forward ThreeRationalFixed318.k=ThreeJModuliOpen318.k := by
  rw [ThreeRationalFixed318.k,map_mul,forward_j,forward_v,ThreeJModuliOpen318.base_ratio]

lemma forward_parameter : forward ThreeRationalFixed318.parameter=ThreeJModuliOpen318.t := by
  have hu := (ThreeNormalizedInverse318.denominator_unit ThreeRationalFixed318.k
    ThreeRationalFixed318.x ThreeRationalFixed318.k_unit ThreeRationalFixed318.k_sub_unit
    ThreeRationalFixed318.root_relation).map forward.toRingHom
  have hi := congrArg forward (ThreeNormalizedInverse318.denominator_inverse
    ThreeRationalFixed318.k ThreeRationalFixed318.x ThreeRationalFixed318.k_unit
    ThreeRationalFixed318.k_sub_unit ThreeRationalFixed318.root_relation)
  simp only [ThreeNormalizedInverse318.denominator,map_sub,map_mul,map_pow,map_ofNat,
    forward_k,forward_x,map_one] at hu hi
  apply hu.mul_left_cancel
  simp only [ThreeRationalFixed318.parameter,ThreeNormalizedInverse318.parameter,
    ThreeNormalizedInverse318.numerator,map_mul,map_sub,map_pow,map_ofNat,forward_k,forward_x]
  have he : 243*(ThreeJModuliOpen318.x^2-ThreeJModuliOpen318.k)=
      ThreeJModuliOpen318.t*(9*ThreeJModuliOpen318.k-ThreeJModuliOpen318.x^2) := by
    unfold ThreeJModuliOpen318.x ThreeJModuliOpen318.k ThreeJModuliOpen318.n
    ring
  linear_combination 243*(ThreeJModuliOpen318.x^2-ThreeJModuliOpen318.k)*hi+he

end ThreeRationalModuliInverse318
