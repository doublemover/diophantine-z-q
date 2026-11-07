module
public import RestrictedEvaluation318
public section
namespace ScaledClosedDisc318
open PowerSeries ScaledCoefficients318 ScaledFormalSeries318 RestrictedEvaluation318
variable (p : ℕ) [Fact p.Prime]

theorem X_restricted : Restricted p (X : PowerSeries ℤ_[p]) :=
  MvPowerSeries.isRestricted_X (fun _ => 1) ()

theorem Hscaled_restricted (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    Restricted p (Hscaled p hp D hD) := by
  apply (isRestricted_iff' 1 _).2
  have hs := (ScaledDecay318.Hscaled_summable p hp D hD 1).tendsto_atTop_zero.norm
  simpa only [one_pow, mul_one, norm_zero] using hs

theorem Bscaled_restricted (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    Restricted p (Bscaled p hp D hD) := by
  apply (isRestricted_iff' 1 _).2
  have hs := (ScaledDecay318.Bscaled_summable p hp D hD 1).tendsto_atTop_zero.norm
  simpa only [one_pow, mul_one, norm_zero] using hs

theorem differentialScaled_restricted (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    Restricted p (differentialScaled p hp D hD) :=
  subst_restricted p _ _ (Bscaled_restricted p hp D hD) ((X_restricted p).pow 4) (by simp)

theorem integralScaled_restricted (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    Restricted p (integralScaled p hp D hD) := by
  apply (X_restricted p).neg.mul
  exact subst_restricted p _ _ (Hscaled_restricted p hp D hD)
    ((X_restricted p).pow 4) (by simp)

theorem branchScaled_restricted (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    Restricted p (branchScaled p hp D hD) := by
  exact ((isRestricted_one 1).sub
    ((isRestricted_C 1 _).mul ((X_restricted p).pow 4))).mul
    (differentialScaled_restricted p hp D hD)

theorem eval_integralScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (t : ℤ_[p]) :
    eval p (integralScaled p hp D hD) t = -t * eval p (Hscaled p hp D hD) (t^4) := by
  have hx := X_restricted p
  have hh := Hscaled_restricted p hp D hD
  rw [integralScaled, eval_mul p _ _ hx.neg (subst_restricted p _ _ hh (hx.pow 4) (by simp)),
    eval_neg, eval_X, eval_subst p _ _ hh (hx.pow 4) (by simp), eval_pow p _ hx, eval_X]

theorem eval_differentialScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (t : ℤ_[p]) :
    eval p (differentialScaled p hp D hD) t = eval p (Bscaled p hp D hD) (t^4) := by
  have hx := X_restricted p
  rw [differentialScaled, eval_subst p _ _ (Bscaled_restricted p hp D hD) (hx.pow 4) (by simp),
    eval_pow p _ hx, eval_X]

theorem eval_branchScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (t : ℤ_[p]) :
    eval p (branchScaled p hp D hD) t =
      (1-parameter p D hD*t^4) * eval p (Bscaled p hp D hD) (t^4) := by
  have hx := X_restricted p
  have hc : Restricted p (C (parameter p D hD)) := isRestricted_C 1 _
  have h1 : Restricted p (1 : PowerSeries ℤ_[p]) := isRestricted_one 1
  rw [branchScaled, eval_mul p _ _ (h1.sub (hc.mul (hx.pow 4)))
    (differentialScaled_restricted p hp D hD),
    eval_sub p _ _ h1 (hc.mul (hx.pow 4)), eval_one,
    eval_mul p _ _ hc (hx.pow 4), eval_C, eval_pow p _ hx, eval_X,
    eval_differentialScaled]

end ScaledClosedDisc318
#print axioms ScaledClosedDisc318.integralScaled_restricted
#print axioms ScaledClosedDisc318.branchScaled_restricted
#print axioms ScaledClosedDisc318.eval_integralScaled
#print axioms ScaledClosedDisc318.eval_branchScaled
