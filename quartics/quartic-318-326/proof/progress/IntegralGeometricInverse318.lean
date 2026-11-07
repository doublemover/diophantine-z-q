module
public import IntegralRingEvaluation318
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public section
namespace IntegralGeometricInverse318
open PowerSeries IntegralRingEvaluation318
variable (R : Type*) [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R]
  [NormBoundOne R]
set_option linter.unusedSectionVars false

@[expose] noncomputable def geometric (a : R) : PowerSeries R :=
  PowerSeries.mk (fun n => (-a)^n)

@[expose] noncomputable def qline (a : R) : PowerSeries R := 1+C a*X^4

@[expose] noncomputable def inverse (a : R) : PowerSeries R :=
  (geometric R a).subst (X^4 : PowerSeries R)

theorem geometric_mul (a : R) : (1+C a*X)*geometric R a = 1 := by
  have he : (1+C a*X)*geometric R a = geometric R a+C a*(geometric R a*X) := by ring
  rw [he]
  ext n
  cases n with
  | zero => simp [geometric]
  | succ n =>
    simp only [map_add, coeff_C_mul, coeff_succ_mul_X, geometric, coeff_mk,
      coeff_one, Nat.succ_ne_zero, ite_false, pow_succ]
    ring

theorem qline_mul_inverse (a : R) : qline R a*inverse R a=1 := by
  have hx : HasSubst (X^4 : PowerSeries R) := .of_constantCoeff_zero
    (by change constantCoeff (X^4 : PowerSeries R)=0; simp)
  have hh := congrArg (substAlgHom (R := R) hx) (geometric_mul R a)
  simp only [map_mul, map_add, map_one, coe_substAlgHom] at hh
  rw [subst_C, subst_X hx] at hh
  change qline R a * inverse R a = 1 at hh
  exact hh

theorem inverse_eq_invOfUnit (a : R) :
    inverse R a = (qline R a).invOfUnit 1 := by
  have hq : constantCoeff (qline R a)=(1 : Rˣ) := by simp [qline]
  calc
    inverse R a = inverse R a*(qline R a*(qline R a).invOfUnit 1) := by rw [MvPowerSeries.mul_invOfUnit _ _ hq, mul_one]
    _ = (qline R a*inverse R a)*(qline R a).invOfUnit 1 := by ring
    _ = (qline R a).invOfUnit 1 := by rw [qline_mul_inverse, one_mul]

theorem geometric_restricted (a : R) (ha : ‖a‖<1) : Restricted R (geometric R a) := by
  apply (isRestricted_iff' 1 _).2
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (show ‖-a‖<1 by simpa only [norm_neg] using ha)).norm
  simpa only [geometric, coeff_mk, one_pow, mul_one, norm_zero] using ht

theorem qline_restricted (a : R) : Restricted R (qline R a) :=
  (isRestricted_one 1).add ((isRestricted_C 1 a).mul ((X_restricted R).pow 4))

theorem inverse_restricted (a : R) (ha : ‖a‖<1) : Restricted R (inverse R a) :=
  subst_restricted R _ _ (geometric_restricted R a ha) ((X_restricted R).pow 4) (by simp)

theorem invOfUnit_restricted (a : R) (ha : ‖a‖<1) :
    Restricted R ((qline R a).invOfUnit 1) := by
  rw [←inverse_eq_invOfUnit]
  exact inverse_restricted R a ha

theorem eval_qline (a t : R) : eval R (qline R a) t = 1+a*t^4 := by
  rw [qline, eval_add R _ _ (isRestricted_one 1)
    ((isRestricted_C 1 a).mul ((X_restricted R).pow 4)), eval_one,
    eval_mul R _ _ (isRestricted_C 1 a) ((X_restricted R).pow 4),
    eval_C, eval_pow R _ (X_restricted R), eval_X]

/-- Genuine analytic inverse identity at every integral t, including units. -/
theorem eval_inverse_mul (a : R) (ha : ‖a‖<1) (t : R) :
    (1+a*t^4)*eval R (inverse R a) t=1 := by
  have hh := congrArg (fun f => eval R f t) (qline_mul_inverse R a)
  simpa only [eval_mul R _ _ (qline_restricted R a) (inverse_restricted R a ha),
    eval_qline, eval_one] using hh


/-- The evaluated inverse under any ring map into an ambient field. -/
theorem eval_inverse_map {K : Type*} [Field K] (φ : R →+* K)
    (a : R) (ha : ‖a‖<1) (t : R) :
    φ (eval R (inverse R a) t) = (1+φ a*(φ t)^4)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have hh := congrArg φ (eval_inverse_mul R a ha t)
  simpa only [map_mul, map_add, map_one, map_pow] using hh

theorem eval_invOfUnit_map {K : Type*} [Field K] (φ : R →+* K)
    (a : R) (ha : ‖a‖<1) (t : R) :
    φ (eval R ((qline R a).invOfUnit 1) t) = (1+φ a*(φ t)^4)⁻¹ := by
  rw [←inverse_eq_invOfUnit]
  exact eval_inverse_map R φ a ha t

end IntegralGeometricInverse318
#print axioms IntegralGeometricInverse318.qline_mul_inverse
#print axioms IntegralGeometricInverse318.invOfUnit_restricted
#print axioms IntegralGeometricInverse318.eval_inverse_mul

#print axioms IntegralGeometricInverse318.eval_invOfUnit_map
