module
public import ThreeRationalFixed318
public section
noncomputable section
namespace ThreeRationalModuliInverse318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def backwardLaurent : ThreeJLaurentEquiv318.Laurent →ₐ[ℚ] ThreeRationalFixed318.Ring :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) ThreeRationalFixed318.parameter)
    (Polynomial.X:ℚ[X]) (by simpa only [Polynomial.aeval_X] using
      ThreeRationalFixed318.parameter_unit)
lemma backwardLaurent_t : backwardLaurent ProjectiveLineOverlap318.t=ThreeRationalFixed318.parameter := by
  simp only [backwardLaurent,ProjectiveLineOverlap318.t,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X]
lemma backwardLaurent_one : backwardLaurent (1:ThreeJLaurentEquiv318.Laurent)=1 :=
  map_one backwardLaurent
lemma backwardLaurent_pow (a : ThreeJLaurentEquiv318.Laurent) (n : ℕ) :
    backwardLaurent (a^n)=(backwardLaurent a)^n := map_pow backwardLaurent a n
lemma backwardLaurent_ts :
    ThreeRationalFixed318.parameter * backwardLaurent ProjectiveLineOverlap318.s=1 := by
  simpa only [map_mul,backwardLaurent_one,backwardLaurent_t] using
    congrArg backwardLaurent ProjectiveLineOverlap318.ts
lemma backwardLaurent_j : backwardLaurent ThreeJLaurentEquiv318.jLaurent=ThreeRationalFixed318.j := by
  simp only [ThreeJLaurentEquiv318.jLaurent,map_mul,backwardLaurent_pow,map_add,map_ofNat,backwardLaurent_t]
  rw [ThreeRationalFixed318.parameter_j,mul_assoc,←mul_pow,backwardLaurent_ts,one_pow,mul_one]
lemma backward_deleted_unit : IsUnit (backwardLaurent ThreeJModuliOpen318.deleted) := by
  rw [ThreeJModuliOpen318.deleted,map_mul,map_sub,map_ofNat,backwardLaurent_j]
  exact ThreeRationalFixed318.j_units.1.mul ThreeRationalFixed318.j_units.2

/-- Constructed inverse on the rational base change of the literal fixed
algebra, using its own quartic relation and unit certificates. -/
@[expose] def backward : ThreeJModuliOpen318.Ring →ₐ[ℚ] ThreeRationalFixed318.Ring :=
  IsLocalization.Away.liftAlgHom (A:=ℚ) (R:=ThreeJLaurentEquiv318.Laurent)
    (S:=ThreeJModuliOpen318.Ring) (P:=ThreeRationalFixed318.Ring) (f:=backwardLaurent) ThreeJModuliOpen318.deleted
    backward_deleted_unit
lemma backward_one : backward (1:ThreeJModuliOpen318.Ring)=1 := map_one backward
lemma backward_pow (a : ThreeJModuliOpen318.Ring) (n : ℕ) :
    backward (a^n)=(backward a)^n := map_pow backward a n
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
  simp only [ThreeJModuliOpen318.d,map_sub,backward_pow,map_mul,map_ofNat,backward_t]
lemma backward_x : backward ThreeJModuliOpen318.x=ThreeRationalFixed318.x := by
  have h := congrArg backward ThreeJModuliOpen318.dv
  simp only [map_mul,backward_one,backward_d] at h
  apply ThreeRationalFixed318.parameter_D_unit.mul_left_cancel
  simp only [ThreeJModuliOpen318.x,map_mul,map_add,map_ofNat,backward_t]
  linear_combination 3*(ThreeRationalFixed318.parameter+27)*
    (ThreeRationalFixed318.parameter+243)*h-ThreeRationalFixed318.parameter_x

/-- The same fixed-algebra ring map with the AMBIENT integer algebra
structures, avoiding an unrelated toIntAlgHom instance at the localization. -/
@[expose] def fixedIntegerMap : ThreeJArithmeticAlgebraMap318.Fixed →ₐ[ℤ] ThreeJModuliOpen318.Ring where
  __ := ThreeJArithmeticAlgebraMap318.fixedMap
  commutes' z := by simp

@[expose] def forward : ThreeRationalFixed318.Ring →ₐ[ℚ] ThreeJModuliOpen318.Ring :=
  AlgHom.liftEquiv ℤ ℚ ThreeJArithmeticAlgebraMap318.Fixed ThreeJModuliOpen318.Ring fixedIntegerMap
lemma forward_one : forward (1:ThreeRationalFixed318.Ring)=1 := map_one forward
lemma forward_pow (a : ThreeRationalFixed318.Ring) (n : ℕ) :
    forward (a^n)=(forward a)^n := map_pow forward a n
lemma forward_fixed (a : ThreeJArithmeticAlgebraMap318.Fixed) :
    forward (ThreeRationalFixed318.includeFixed a)=ThreeJArithmeticAlgebraMap318.fixedMap a := by
  change forward (1 ⊗ₜ[ℤ] a)=_
  simp only [forward,AlgHom.liftEquiv_tmul,one_smul]
  rfl
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
  simp only [ThreeNormalizedInverse318.denominator,AlgHom.coe_toRingHom,map_sub,map_mul,forward_pow,map_ofNat,
    forward_k,forward_x,forward_one] at hu hi
  apply hu.mul_left_cancel
  simp only [ThreeRationalFixed318.parameter,ThreeNormalizedInverse318.parameter,
    ThreeNormalizedInverse318.numerator,map_mul,map_sub,forward_pow,map_ofNat,forward_k,forward_x]
  have he : 243*(ThreeJModuliOpen318.x^2-ThreeJModuliOpen318.k)=
      ThreeJModuliOpen318.t*(9*ThreeJModuliOpen318.k-ThreeJModuliOpen318.x^2) := by
    unfold ThreeJModuliOpen318.x ThreeJModuliOpen318.k ThreeJModuliOpen318.n
    ring
  linear_combination 243*(ThreeJModuliOpen318.x^2-ThreeJModuliOpen318.k)*hi+he

end ThreeRationalModuliInverse318
