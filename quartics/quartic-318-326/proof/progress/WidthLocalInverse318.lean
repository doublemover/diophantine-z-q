module
public import RotatedHomeomorph318
public section
noncomputable section
open Function Filter Topology
open scoped ContDiff
namespace WidthLocalInverse318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def derivative (w:ℝ) (hw:0<w) (z:ℂ) : ℂ := (2*Real.pi*Complex.I/w)*Periodic.qParam w z

theorem q_hasDerivAt (w:ℝ) (hw:0<w) (z:ℂ) : HasDerivAt (Periodic.qParam w) (derivative w hw z) z := by
  have h := (Complex.hasDerivAt_exp ((2*Real.pi*Complex.I/w)*z)).comp z
    ((hasDerivAt_id z).const_mul (2*Real.pi*Complex.I/w))
  have he : Periodic.qParam w = fun v:ℂ => Complex.exp ((2*Real.pi*Complex.I/w)*v) := by
    funext v
    simp only [Periodic.qParam]
    congr 1
    ring
  simpa [derivative,he,Function.comp_def,mul_comm] using! h

theorem q_analytic (w:ℝ) (hw:0<w) (z:ℂ) : AnalyticAt ℂ (Periodic.qParam w) z :=
  (Periodic.contDiff_qParam (h:=w) ω).contDiffAt.analyticAt

theorem q_derivative_ne_zero (w:ℝ) (hw:0<w) (z:ℂ) : deriv (Periodic.qParam w) z ≠ 0 := by
  rw [(q_hasDerivAt w hw z).deriv]
  exact mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne')) (Periodic.qParam_ne_zero _)

/-- A genuine analytic local logarithm of the q-parameter at any chosen lift,
without requiring the principal logarithm to be continuous on a whole annulus. -/
@[expose] def inverse (w:ℝ) (hw:0<w) (z:ℂ) : ℂ→ℂ :=
  (q_analytic w hw z).hasStrictDerivAt.localInverse _ _ _ (q_derivative_ne_zero w hw z)

theorem inverse_analytic (w:ℝ) (hw:0<w) (z:ℂ) : AnalyticAt ℂ (inverse w hw z) (Periodic.qParam w z) := by
  simpa only [inverse] using! (q_analytic w hw z).analyticAt_localInverse (q_derivative_ne_zero w hw z)

theorem inverse_value (w:ℝ) (hw:0<w) (z:ℂ) : inverse w hw z (Periodic.qParam w z)=z := by
  exact HasStrictFDerivAt.localInverse_apply_image
    ((q_analytic w hw z).hasStrictDerivAt.hasStrictFDerivAt_equiv (q_derivative_ne_zero w hw z))

theorem inverse_right (w:ℝ) (hw:0<w) (z:ℂ) : ∀ᶠq in 𝓝 (Periodic.qParam w z),
    Periodic.qParam w (inverse w hw z q)=q :=
  HasStrictDerivAt.eventually_right_inverse
    (hf:=(q_analytic w hw z).hasStrictDerivAt) (hf':=q_derivative_ne_zero w hw z)

end WidthLocalInverse318
