module
public import Mathlib
public section
noncomputable section
namespace ActualTZCollisionLogEnvelope318
open Filter Asymptotics
open scoped Topology

/-- Only a fixed exponent has been chosen before y. The polynomial
loss p^(1/4) replaces Chebyshev partial summation in the finite
arithmetic tail, still leaving a power of N on the correct side. -/
theorem eventually_quarter (A : ℝ) (hA : 0≤A) :
    ∃ Y : ℝ,∀ x≥Y,(1+Real.log x)^A≤x^((1:ℝ)/4) := by
  have hPow : 0<(2:ℝ)^A := Real.rpow_pos_of_pos (by norm_num) _
  have h₀ := _root_.isLittleO_log_rpow_rpow_atTop A (by norm_num : 0<(1:ℝ)/4)
  have h := h₀.bound (one_div_pos.mpr hPow)
  have H : ∀ᶠ x : ℝ in atTop,(1+Real.log x)^A≤x^((1:ℝ)/4) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1),h] with x hx hX
    have hp : 0<x := (Real.exp_pos 1).trans_le hx
    have hLog : 1≤Real.log x := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
    have hLog0 : 0≤Real.log x := zero_le_one.trans hLog
    have h1 : 0≤(Real.log x)^A := Real.rpow_nonneg hLog0 _
    have h2 : 0≤x^((1:ℝ)/4) := Real.rpow_nonneg hp.le _
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg h1,abs_of_nonneg h2] at hX
    calc
      _ ≤ (2*Real.log x)^A :=
        Real.rpow_le_rpow (by positivity) (by linarith) hA
      _ = (2:ℝ)^A*(Real.log x)^A := Real.mul_rpow (by norm_num) hLog0
      _ ≤ _ := by
        have hM := mul_le_mul_of_nonneg_left hX hPow.le
        simpa only [mul_assoc,one_div,mul_inv_cancel₀ hPow.ne',one_mul] using hM
  exact eventually_atTop.mp H

end ActualTZCollisionLogEnvelope318
