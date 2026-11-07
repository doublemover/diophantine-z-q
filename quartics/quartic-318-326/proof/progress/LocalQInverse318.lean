module
public import HolomorphicCuspChart318
public section
noncomputable section
open Function Filter Topology
open scoped ContDiff
namespace LocalQInverse318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def derivative (z:ℂ) : ℂ := 2*Real.pi*Complex.I*Periodic.qParam 1 z

theorem q_hasDerivAt (z:ℂ) : HasDerivAt (Periodic.qParam 1) (derivative z) z := by
  have h := (Complex.hasDerivAt_exp ((2*Real.pi*Complex.I)*z)).comp z
    ((hasDerivAt_id z).const_mul (2*Real.pi*Complex.I))
  have he : Periodic.qParam 1 = fun w:ℂ => Complex.exp ((2*Real.pi*Complex.I)*w) := by
    funext w
    simp [Periodic.qParam]
  simpa [derivative,he,Function.comp_def,mul_comm] using! h

theorem q_analytic (z:ℂ) : AnalyticAt ℂ (Periodic.qParam 1) z :=
  (Periodic.contDiff_qParam (h:=1) ω).contDiffAt.analyticAt

theorem q_derivative_ne_zero (z:ℂ) : deriv (Periodic.qParam 1) z ≠ 0 := by
  rw [(q_hasDerivAt z).deriv]
  exact mul_ne_zero Complex.two_pi_I_ne_zero (Periodic.qParam_ne_zero _)

/-- A genuine analytic local logarithm of the q-parameter at any chosen lift,
without requiring the principal logarithm to be continuous on a whole annulus. -/
@[expose] def inverse (z:ℂ) : ℂ→ℂ :=
  (q_analytic z).hasStrictDerivAt.localInverse _ _ _ (q_derivative_ne_zero z)

theorem inverse_analytic (z:ℂ) : AnalyticAt ℂ (inverse z) (Periodic.qParam 1 z) := by
  simpa only [inverse] using! (q_analytic z).analyticAt_localInverse (q_derivative_ne_zero z)

theorem inverse_value (z:ℂ) : inverse z (Periodic.qParam 1 z)=z := by
  exact HasStrictFDerivAt.localInverse_apply_image
    ((q_analytic z).hasStrictDerivAt.hasStrictFDerivAt_equiv (q_derivative_ne_zero z))

theorem inverse_right (z:ℂ) : ∀ᶠq in 𝓝 (Periodic.qParam 1 z),
    Periodic.qParam 1 (inverse z q)=q :=
  HasStrictDerivAt.eventually_right_inverse
    (hf:=(q_analytic z).hasStrictDerivAt) (hf':=q_derivative_ne_zero z)

end LocalQInverse318
