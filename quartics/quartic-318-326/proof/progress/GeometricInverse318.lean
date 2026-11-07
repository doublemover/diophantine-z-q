module
public import ScaledClosedDisc318
public section
namespace GeometricInverse318
open PowerSeries RestrictedEvaluation318 ScaledClosedDisc318
variable (p : ℕ) [Fact p.Prime]

@[expose] noncomputable def geometric (a : ℤ_[p]) : PowerSeries ℤ_[p] :=
  PowerSeries.mk (fun n => (-a)^n)

@[expose] noncomputable def qline (a : ℤ_[p]) : PowerSeries ℤ_[p] := 1+C a*X^4

@[expose] noncomputable def inverse (a : ℤ_[p]) : PowerSeries ℤ_[p] :=
  (geometric p a).subst (X^4 : PowerSeries ℤ_[p])

theorem geometric_mul (a : ℤ_[p]) : (1+C a*X)*geometric p a = 1 := by
  have he : (1+C a*X)*geometric p a = geometric p a+C a*(geometric p a*X) := by ring
  rw [he]
  ext n
  cases n with
  | zero => simp [geometric]
  | succ n =>
    simp only [map_add, coeff_C_mul, coeff_succ_mul_X, geometric, coeff_mk,
      coeff_one, Nat.succ_ne_zero, ite_false, pow_succ]
    ring

theorem qline_mul_inverse (a : ℤ_[p]) : qline p a*inverse p a=1 := by
  have hx : HasSubst (X^4 : PowerSeries ℤ_[p]) := .of_constantCoeff_zero
    (by change constantCoeff (X^4 : PowerSeries ℤ_[p])=0; simp)
  have hh := congrArg (substAlgHom (R := ℤ_[p]) hx) (geometric_mul p a)
  simp only [map_mul, map_add, map_one, coe_substAlgHom] at hh
  rw [subst_C, subst_X hx] at hh
  change qline p a * inverse p a = 1 at hh
  exact hh

theorem inverse_eq_invOfUnit (a : ℤ_[p]) :
    inverse p a = (qline p a).invOfUnit 1 := by
  have hq : constantCoeff (qline p a)=(1 : ℤ_[p]ˣ) := by simp [qline]
  calc
    inverse p a = inverse p a*(qline p a*(qline p a).invOfUnit 1) := by rw [MvPowerSeries.mul_invOfUnit _ _ hq, mul_one]
    _ = (qline p a*inverse p a)*(qline p a).invOfUnit 1 := by ring
    _ = (qline p a).invOfUnit 1 := by rw [qline_mul_inverse, one_mul]

theorem geometric_restricted (a : ℤ_[p]) (ha : ‖a‖<1) : Restricted p (geometric p a) := by
  apply (isRestricted_iff' 1 _).2
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (show ‖-a‖<1 by simpa only [norm_neg] using ha)).norm
  simpa only [geometric, coeff_mk, one_pow, mul_one, norm_zero] using ht

theorem qline_restricted (a : ℤ_[p]) : Restricted p (qline p a) :=
  (isRestricted_one 1).add ((isRestricted_C 1 a).mul ((X_restricted p).pow 4))

theorem inverse_restricted (a : ℤ_[p]) (ha : ‖a‖<1) : Restricted p (inverse p a) :=
  subst_restricted p _ _ (geometric_restricted p a ha) ((X_restricted p).pow 4) (by simp)

theorem invOfUnit_restricted (a : ℤ_[p]) (ha : ‖a‖<1) :
    Restricted p ((qline p a).invOfUnit 1) := by
  rw [←inverse_eq_invOfUnit]
  exact inverse_restricted p a ha

theorem eval_qline (a t : ℤ_[p]) : eval p (qline p a) t = 1+a*t^4 := by
  rw [qline, eval_add p _ _ (isRestricted_one 1)
    ((isRestricted_C 1 a).mul ((X_restricted p).pow 4)), eval_one,
    eval_mul p _ _ (isRestricted_C 1 a) ((X_restricted p).pow 4),
    eval_C, eval_pow p _ (X_restricted p), eval_X]

/-- Genuine analytic inverse identity at every integral t, including units. -/
theorem eval_inverse_mul (a : ℤ_[p]) (ha : ‖a‖<1) (t : ℤ_[p]) :
    (1+a*t^4)*eval p (inverse p a) t=1 := by
  have hh := congrArg (fun f => eval p f t) (qline_mul_inverse p a)
  simpa only [eval_mul p _ _ (qline_restricted p a) (inverse_restricted p a ha),
    eval_qline, eval_one] using hh


/-- The same evaluated inverse as an ordinary inverse in the ambient Qp field. -/
theorem eval_inverse_coe (a : ℤ_[p]) (ha : ‖a‖<1) (t : ℤ_[p]) :
    (eval p (inverse p a) t : ℚ_[p]) = (1+(a : ℚ_[p])*(t : ℚ_[p])^4)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have hh := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (eval_inverse_mul p a ha t)
  simpa only [PadicInt.coe_mul, PadicInt.coe_add, PadicInt.coe_one, PadicInt.coe_pow] using hh

/-- Consumer-facing version using the source formal inverse itself. -/
theorem eval_invOfUnit_coe (a : ℤ_[p]) (ha : ‖a‖<1) (t : ℤ_[p]) :
    (eval p ((qline p a).invOfUnit 1) t : ℚ_[p]) =
      (1+(a : ℚ_[p])*(t : ℚ_[p])^4)⁻¹ := by
  rw [←inverse_eq_invOfUnit]
  exact eval_inverse_coe p a ha t

end GeometricInverse318
#print axioms GeometricInverse318.qline_mul_inverse
#print axioms GeometricInverse318.invOfUnit_restricted
#print axioms GeometricInverse318.eval_inverse_mul

#print axioms GeometricInverse318.eval_invOfUnit_coe
