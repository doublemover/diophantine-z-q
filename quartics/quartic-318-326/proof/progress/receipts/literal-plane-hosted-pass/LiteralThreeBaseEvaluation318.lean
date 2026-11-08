module
public import ArithmeticPointTopology318
public section
noncomputable section
namespace LiteralThreeBaseEvaluation318
open Polynomial OpenJModel318 OpenJAffineScheme318 ModularCoordinateProper318
set_option maxHeartbeats 0

@[expose] def polynomialEval (z : JOpen) : ℤ[X] →+* ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℂ) z.val

lemma denominator_isUnit (N : ℕ) [NeZero N] (z : JOpen) :
    IsUnit (polynomialEval z (denominator N)) := by
  apply isUnit_iff_ne_zero.mpr
  have hN : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simpa [polynomialEval,denominator,sub_ne_zero] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6:ℂ)≠0) hN) z.property.1)
      (sub_ne_zero.mpr z.property.2)

/-- Evaluation at an arbitrary point of the literal open j-line. No analytic
period representative or j-surjectivity theorem is needed to construct it. -/
@[expose] def evaluation (N : ℕ) [NeZero N] (z : JOpen) : Base N →+* ℂ :=
  IsLocalization.Away.lift (denominator N) (denominator_isUnit N z)

@[simp] lemma evaluation_j (N : ℕ) [NeZero N] (z : JOpen) :
    evaluation N z (jCoord N)=z.val := by
  simp [evaluation,jCoord,polynomialEval]

lemma evaluation_inverse (N : ℕ) [NeZero N] (z : JOpen) :
    evaluation N z (inverseDenominator N)=(z.val-1728)⁻¹ := by
  have he := congrArg (evaluation N z) (denominator_inverse N)
  simp only [map_mul,map_sub,map_ofNat,map_one,evaluation_j] at he
  exact (inv_eq_of_mul_eq_one_right he).symm

lemma hom_ext (N : ℕ) [NeZero N] (f g : Base N →+* ℂ)
    (hj : f (jCoord N)=g (jCoord N)) : f=g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · exact hj

lemma evaluation_A (N : ℕ) [NeZero N] (z : JOpen) :
    evaluation N z (A N)= -3*z.val/(z.val-1728) := by
  simp only [A,map_mul,map_neg,map_ofNat,evaluation_j,evaluation_inverse,div_eq_mul_inv]

lemma evaluation_B (N : ℕ) [NeZero N] (z : JOpen) :
    evaluation N z (B N)= -2*z.val/(z.val-1728) := by
  simp only [B,map_mul,map_neg,map_ofNat,evaluation_j,evaluation_inverse,div_eq_mul_inv]

/-- The literal affine quartic after clearing the invertible j-1728 denominator. -/
@[expose] def Q (z x : ℂ) : ℂ :=
  (z-1728)^2*x^4-6*z*(z-1728)*x^2-8*z*(z-1728)*x-3*z^2

lemma division_eval (N : ℕ) [NeZero N] (z : JOpen) (x : ℂ) :
    (ThreeTorsionIdentity318.divisionPolynomial (evaluation N z (A N))
      (evaluation N z (B N))).eval x=3*Q z.val x/(z.val-1728)^2 := by
  simp only [ThreeTorsionIdentity318.divisionPolynomial,eval_sub,eval_add,eval_mul,
    eval_pow,eval_ofNat,eval_X,eval_C,evaluation_A,evaluation_B,Q]
  field_simp [sub_ne_zero.mpr z.property.2]
  <;> ring

lemma division_zero_iff (N : ℕ) [NeZero N] (z : JOpen) (x : ℂ) :
    (ThreeTorsionIdentity318.divisionPolynomial (evaluation N z (A N))
      (evaluation N z (B N))).eval x=0 ↔ Q z.val x=0 := by
  simp [division_eval,sub_ne_zero.mpr z.property.2]

end LiteralThreeBaseEvaluation318
