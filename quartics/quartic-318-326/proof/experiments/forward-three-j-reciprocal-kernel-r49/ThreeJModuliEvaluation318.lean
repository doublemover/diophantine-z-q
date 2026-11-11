module
public import ThreeJModuliScheme318
public import LiteralThreeCompactParameter318
public section
noncomputable section
namespace ThreeJModuliEvaluation318
open Polynomial ThreeJModuliOpen318 ThreeJArithmeticAlgebraMap318
open ThreeCompactParameter318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def laurentEvaluation (z : ParameterOpen) : ThreeJLaurentEquiv318.Laurent →ₐ[ℚ] ℂ :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) z.val) (Polynomial.X:ℚ[X])
    (by simpa only [Polynomial.aeval_X] using isUnit_iff_ne_zero.mpr z.property.1)
lemma laurent_t (z : ParameterOpen) :
    laurentEvaluation z ProjectiveLineOverlap318.t=z.val := by
  simp only [laurentEvaluation,ProjectiveLineOverlap318.t,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  change Polynomial.aeval (R:=ℚ) z.val Polynomial.X=z.val
  exact Polynomial.aeval_X z.val
lemma laurent_s (z : ParameterOpen) :
    laurentEvaluation z ProjectiveLineOverlap318.s=z.val⁻¹ := by
  have h := congrArg (laurentEvaluation z) ProjectiveLineOverlap318.ts
  simp only [map_mul,map_one,laurent_t] at h
  exact (inv_eq_of_mul_eq_one_right h).symm
lemma laurent_j (z : ParameterOpen) :
    laurentEvaluation z ThreeJLaurentEquiv318.jLaurent=J z.val := by
  simp only [ThreeJLaurentEquiv318.jLaurent,map_mul,map_add,map_pow,map_ofNat,
    laurent_t,laurent_s,J,div_eq_mul_inv,inv_pow]
lemma deleted_unit (z : ParameterOpen) : IsUnit (laurentEvaluation z deleted) := by
  rw [deleted,map_mul,map_sub,map_ofNat,laurent_j]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero
    ((J_ne_zero_iff z.property.1).mpr ⟨z.property.2.1,z.property.2.2.1⟩)
    (sub_ne_zero.mpr ((J_ne_1728_iff z.property.1).mpr z.property.2.2.2)))
@[expose] def evaluation (z : ParameterOpen) : Ring →ₐ[ℚ] ℂ :=
  IsLocalization.Away.liftAlgHom (f:=laurentEvaluation z) deleted (deleted_unit z)
lemma evaluation_inclusion (z : ParameterOpen) (a : ThreeJLaurentEquiv318.Laurent) :
    evaluation z (inclusion a)=laurentEvaluation z a := by
  simp only [evaluation,inclusion,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  change laurentEvaluation z a=laurentEvaluation z a
  rfl
lemma evaluation_t (z : ParameterOpen) : evaluation z t=z.val := by
  rw [t,evaluation_inclusion,laurent_t]
lemma evaluation_s (z : ParameterOpen) : evaluation z s=z.val⁻¹ := by
  rw [s,evaluation_inclusion,laurent_s]
lemma evaluation_j (z : ParameterOpen) : evaluation z j=J z.val := by
  rw [j,evaluation_inclusion,laurent_j]
lemma evaluation_d (z : ParameterOpen) : evaluation z d=D z.val := by
  simp only [d,D,map_sub,map_mul,map_pow,map_ofNat,evaluation_t]
lemma evaluation_v (z : ParameterOpen) : evaluation z v=(D z.val)⁻¹ := by
  have h := congrArg (evaluation z) dv
  simp only [map_mul,map_one,evaluation_d] at h
  exact (inv_eq_of_mul_eq_one_right h).symm
lemma evaluation_x (z : ParameterOpen) : evaluation z x=ThreeCompactParameter318.X z.val := by
  simp only [x,ThreeCompactParameter318.X,map_mul,map_add,map_ofNat,evaluation_t,
    evaluation_v,div_eq_mul_inv]

/-- Evaluation of the constructed scheme map is exactly the old arithmetic
comparison on the entire admissible quotient, including its original x marker. -/
theorem arithmetic_evaluation (z : ParameterOpen) :
    (evaluation z).toRingHom.comp fixedMap=
      ThreeArithmeticQuotient318.complexPoint 3
        ((LiteralThreeCompactParameter318.sourceParameter 3).symm z) := by
  apply ModularArithmeticCoordinates318.hom_ext 3
  · change evaluation z (fixedMap _)=_
    rw [fixedMap_j,evaluation_j,ThreeArithmeticQuotient318.complexPoint_j]
    exact (LiteralThreeCompactParameter318.sourceParameter_inverse_j 3 z).symm
  · change evaluation z (fixedMap _)=_
    rw [fixedMap_x,evaluation_x,ModularArithmeticCoordinates318.complexPoint_x]
    exact (LiteralThreeCompactParameter318.sourceParameter_inverse_x 3 z).symm

/-- The induced map covers every original fixed-algebra complex point
exactly once. This is a theorem about points, not a substituted scheme-isomorphism claim. -/
theorem arithmetic_evaluation_bijective : Function.Bijective
    (fun z : ParameterOpen => (evaluation z).toRingHom.comp fixedMap) := by
  have h : (fun z : ParameterOpen => (evaluation z).toRingHom.comp fixedMap)=
      ThreeArithmeticQuotient318.complexPoint 3 ∘
        (LiteralThreeCompactParameter318.sourceParameter 3).symm :=
    funext arithmetic_evaluation
  rw [h]
  exact ⟨(ArithmeticComparisonInjective318.complexPoint_injective 3).comp
      (LiteralThreeCompactParameter318.sourceParameter 3).symm.injective,
    (ThreeArithmeticSurjective318.complexPoint_surjective 3).comp
      (LiteralThreeCompactParameter318.sourceParameter 3).symm.surjective⟩

end ThreeJModuliEvaluation318
